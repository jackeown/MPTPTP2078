%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:12 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 391 expanded)
%              Number of leaves         :   31 ( 164 expanded)
%              Depth                    :   17
%              Number of atoms          : 1019 (2192 expanded)
%              Number of equality atoms :   57 (  93 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f495,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f82,f86,f90,f94,f98,f112,f116,f127,f206,f235,f251,f265,f275,f324,f358,f394,f440,f465,f486])).

fof(f486,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_45 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | spl6_8
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f484,f81])).

fof(f81,plain,
    ( ~ r2_hidden(sK1,sK4)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_8
  <=> r2_hidden(sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f484,plain,
    ( r2_hidden(sK1,sK4)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_32
    | ~ spl6_33
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f483,f357])).

fof(f357,plain,
    ( sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl6_33
  <=> sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f483,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_32
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f482,f73])).

fof(f73,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl6_6
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f482,plain,
    ( ~ r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_15
    | ~ spl6_32
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f481,f97])).

fof(f97,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_12
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f481,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_32
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f477,f323])).

fof(f323,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl6_32
  <=> m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f477,plain,
    ( ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_45 ),
    inference(resolution,[],[f464,f160])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ r2_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k3_orders_2(sK0,sK3,X1)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f159,f53])).

fof(f53,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k3_orders_2(sK0,sK3,X1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f158,f69])).

fof(f69,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k3_orders_2(sK0,sK3,X1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f157,f65])).

fof(f65,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k3_orders_2(sK0,sK3,X1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f156,f61])).

fof(f61,plain,
    ( v4_orders_2(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl6_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k3_orders_2(sK0,sK3,X1)) )
    | ~ spl6_2
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f152,f57])).

fof(f57,plain,
    ( v3_orders_2(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,sK3)
        | r2_hidden(X0,k3_orders_2(sK0,sK3,X1)) )
    | ~ spl6_15 ),
    inference(resolution,[],[f126,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f126,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f464,plain,
    ( r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl6_45
  <=> r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f465,plain,
    ( spl6_45
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_32
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f446,f438,f322,f110,f96,f92,f68,f64,f60,f463])).

fof(f92,plain,
    ( spl6_11
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f110,plain,
    ( spl6_13
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f438,plain,
    ( spl6_44
  <=> r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f446,plain,
    ( r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_32
    | ~ spl6_44 ),
    inference(subsumption_resolution,[],[f441,f323])).

fof(f441,plain,
    ( ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4))
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(resolution,[],[f439,f123])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ r2_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,sK1,X0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f122,f61])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r2_orders_2(sK0,sK2,X0)
        | r2_orders_2(sK0,sK1,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f121,f93])).

fof(f93,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r2_orders_2(sK0,sK2,X0)
        | r2_orders_2(sK0,sK1,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f120,f97])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r2_orders_2(sK0,sK2,X0)
        | r2_orders_2(sK0,sK1,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f119,f69])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r2_orders_2(sK0,sK2,X0)
        | r2_orders_2(sK0,sK1,X0) )
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f118,f65])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v4_orders_2(sK0)
        | ~ r2_orders_2(sK0,sK2,X0)
        | r2_orders_2(sK0,sK1,X0) )
    | ~ spl6_13 ),
    inference(resolution,[],[f111,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_orders_2(X0)
      | ~ r2_orders_2(X0,X2,X3)
      | r2_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).

fof(f111,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f439,plain,
    ( r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f438])).

fof(f440,plain,
    ( spl6_44
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_32
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f432,f356,f322,f125,f92,f76,f68,f64,f60,f56,f52,f438])).

fof(f76,plain,
    ( spl6_7
  <=> r2_hidden(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f432,plain,
    ( r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_32
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f429,f77])).

fof(f77,plain,
    ( r2_hidden(sK2,sK4)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f429,plain,
    ( ~ r2_hidden(sK2,sK4)
    | r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_32
    | ~ spl6_33 ),
    inference(resolution,[],[f410,f93])).

fof(f410,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK4)
        | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_32
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f409,f53])).

fof(f409,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15
    | ~ spl6_32
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f408,f126])).

fof(f408,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_32
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f407,f323])).

fof(f407,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f406,f69])).

fof(f406,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f405,f65])).

fof(f405,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f404,f61])).

fof(f404,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_2
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f401,f57])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4)
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))
        | v2_struct_0(sK0) )
    | ~ spl6_33 ),
    inference(superposition,[],[f36,f357])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f394,plain,
    ( spl6_16
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_26
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f392,f263,f249,f114,f68,f64,f60,f56,f52,f177])).

fof(f177,plain,
    ( spl6_16
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f114,plain,
    ( spl6_14
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f249,plain,
    ( spl6_26
  <=> m1_orders_2(sK4,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f263,plain,
    ( spl6_28
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f392,plain,
    ( k1_xboole_0 = sK4
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_26
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f389,f250])).

fof(f250,plain,
    ( m1_orders_2(sK4,sK0,k1_xboole_0)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f249])).

fof(f389,plain,
    ( k1_xboole_0 = sK4
    | ~ m1_orders_2(sK4,sK0,k1_xboole_0)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_28 ),
    inference(resolution,[],[f349,f115])).

fof(f115,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f114])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f348,f53])).

fof(f348,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f347,f69])).

fof(f347,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f346,f65])).

fof(f346,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f345,f61])).

fof(f345,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl6_2
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f337,f57])).

fof(f337,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ m1_orders_2(X0,sK0,k1_xboole_0) )
    | ~ spl6_28 ),
    inference(resolution,[],[f264,f44])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

fof(f264,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f263])).

fof(f358,plain,
    ( spl6_33
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f318,f273,f114,f88,f356])).

fof(f88,plain,
    ( spl6_10
  <=> m1_orders_2(sK4,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f273,plain,
    ( spl6_30
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X4,sK0,sK3)
        | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f318,plain,
    ( sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f316,f89])).

fof(f89,plain,
    ( m1_orders_2(sK4,sK0,sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f316,plain,
    ( ~ m1_orders_2(sK4,sK0,sK3)
    | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(resolution,[],[f274,f115])).

fof(f274,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X4,sK0,sK3)
        | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4 )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f273])).

fof(f324,plain,
    ( spl6_32
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f254,f233,f114,f88,f322])).

fof(f233,plain,
    ( spl6_25
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X2,sK0,sK3)
        | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f254,plain,
    ( m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f252,f89])).

fof(f252,plain,
    ( ~ m1_orders_2(sK4,sK0,sK3)
    | m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(resolution,[],[f234,f115])).

fof(f234,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X2,sK0,sK3)
        | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0)) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f233])).

fof(f275,plain,
    ( spl6_20
    | spl6_30
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f175,f125,f68,f64,f60,f56,f52,f273,f193])).

fof(f193,plain,
    ( spl6_20
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f175,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4
        | ~ m1_orders_2(X4,sK0,sK3) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f174,f53])).

fof(f174,plain,
    ( ! [X4] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4
        | ~ m1_orders_2(X4,sK0,sK3) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f173,f69])).

fof(f173,plain,
    ( ! [X4] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4
        | ~ m1_orders_2(X4,sK0,sK3) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f172,f65])).

fof(f172,plain,
    ( ! [X4] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4
        | ~ m1_orders_2(X4,sK0,sK3) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f171,f61])).

fof(f171,plain,
    ( ! [X4] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4
        | ~ m1_orders_2(X4,sK0,sK3) )
    | ~ spl6_2
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f155,f57])).

fof(f155,plain,
    ( ! [X4] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4
        | ~ m1_orders_2(X4,sK0,sK3) )
    | ~ spl6_15 ),
    inference(resolution,[],[f126,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f265,plain,
    ( spl6_28
    | ~ spl6_15
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f199,f193,f125,f263])).

fof(f199,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_15
    | ~ spl6_20 ),
    inference(superposition,[],[f126,f194])).

fof(f194,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f193])).

fof(f251,plain,
    ( spl6_26
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f200,f193,f88,f249])).

fof(f200,plain,
    ( m1_orders_2(sK4,sK0,k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(superposition,[],[f89,f194])).

fof(f235,plain,
    ( spl6_20
    | spl6_25
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f165,f125,f68,f64,f60,f56,f52,f233,f193])).

fof(f165,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0))
        | ~ m1_orders_2(X2,sK0,sK3) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f164,f53])).

fof(f164,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0))
        | ~ m1_orders_2(X2,sK0,sK3) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f163,f69])).

fof(f163,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0))
        | ~ m1_orders_2(X2,sK0,sK3) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f162,f65])).

fof(f162,plain,
    ( ! [X2] :
        ( ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0))
        | ~ m1_orders_2(X2,sK0,sK3) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f161,f61])).

fof(f161,plain,
    ( ! [X2] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0))
        | ~ m1_orders_2(X2,sK0,sK3) )
    | ~ spl6_2
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f153,f57])).

fof(f153,plain,
    ( ! [X2] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3
        | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0))
        | ~ m1_orders_2(X2,sK0,sK3) )
    | ~ spl6_15 ),
    inference(resolution,[],[f126,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f206,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != sK4
    | r2_hidden(sK1,sK4)
    | ~ r2_hidden(sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f127,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f22,f125])).

fof(f22,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,X0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r2_hidden(X1,X4)
                      & m1_orders_2(X4,X0,X3)
                      & r2_hidden(X2,X4)
                      & r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
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
                   => ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( ( m1_orders_2(X4,X0,X3)
                            & r2_hidden(X2,X4)
                            & r2_hidden(X1,X3)
                            & r2_orders_2(X0,X1,X2) )
                         => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( ( m1_orders_2(X4,X0,X3)
                          & r2_hidden(X2,X4)
                          & r2_hidden(X1,X3)
                          & r2_orders_2(X0,X1,X2) )
                       => r2_hidden(X1,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_orders_2)).

fof(f116,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f16,f114])).

fof(f16,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f112,plain,
    ( spl6_13
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f103,f96,f92,f84,f68,f110])).

fof(f84,plain,
    ( spl6_9
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f103,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f102,f69])).

fof(f102,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl6_9
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f101,f93])).

fof(f101,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f99,f97])).

fof(f99,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl6_9 ),
    inference(resolution,[],[f85,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f85,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f98,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f24,f96])).

fof(f24,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f94,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f23,f92])).

fof(f23,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f90,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f20,f88])).

fof(f20,plain,(
    m1_orders_2(sK4,sK0,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f17,f84])).

fof(f17,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f82,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f21,f80])).

fof(f21,plain,(
    ~ r2_hidden(sK1,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f78,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f19,f76])).

fof(f19,plain,(
    r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f8])).

fof(f74,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f18,f72])).

fof(f18,plain,(
    r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f70,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f28,f64])).

fof(f28,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f26,f56])).

fof(f26,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f54,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n005.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 11:20:02 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.19/0.43  % (24506)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.43  % (24510)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.43  % (24505)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.43  % (24506)Refutation not found, incomplete strategy% (24506)------------------------------
% 0.19/0.43  % (24506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.43  % (24506)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.43  
% 0.19/0.43  % (24506)Memory used [KB]: 10618
% 0.19/0.43  % (24506)Time elapsed: 0.064 s
% 0.19/0.43  % (24506)------------------------------
% 0.19/0.43  % (24506)------------------------------
% 0.19/0.43  % (24522)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.44  % (24514)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.44  % (24525)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.44  % (24527)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.44  % (24527)Refutation not found, incomplete strategy% (24527)------------------------------
% 0.19/0.44  % (24527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (24527)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.44  
% 0.19/0.44  % (24527)Memory used [KB]: 10618
% 0.19/0.44  % (24527)Time elapsed: 0.074 s
% 0.19/0.44  % (24527)------------------------------
% 0.19/0.44  % (24527)------------------------------
% 0.19/0.44  % (24512)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.45  % (24519)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.45  % (24505)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f495,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f70,f74,f78,f82,f86,f90,f94,f98,f112,f116,f127,f206,f235,f251,f265,f275,f324,f358,f394,f440,f465,f486])).
% 0.19/0.45  fof(f486,plain,(
% 0.19/0.45    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_8 | ~spl6_12 | ~spl6_15 | ~spl6_32 | ~spl6_33 | ~spl6_45),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f485])).
% 0.19/0.45  fof(f485,plain,(
% 0.19/0.45    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | spl6_8 | ~spl6_12 | ~spl6_15 | ~spl6_32 | ~spl6_33 | ~spl6_45)),
% 0.19/0.45    inference(subsumption_resolution,[],[f484,f81])).
% 0.19/0.45  fof(f81,plain,(
% 0.19/0.45    ~r2_hidden(sK1,sK4) | spl6_8),
% 0.19/0.45    inference(avatar_component_clause,[],[f80])).
% 0.19/0.45  fof(f80,plain,(
% 0.19/0.45    spl6_8 <=> r2_hidden(sK1,sK4)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.19/0.45  fof(f484,plain,(
% 0.19/0.45    r2_hidden(sK1,sK4) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_15 | ~spl6_32 | ~spl6_33 | ~spl6_45)),
% 0.19/0.45    inference(forward_demodulation,[],[f483,f357])).
% 0.19/0.45  fof(f357,plain,(
% 0.19/0.45    sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) | ~spl6_33),
% 0.19/0.45    inference(avatar_component_clause,[],[f356])).
% 0.19/0.45  fof(f356,plain,(
% 0.19/0.45    spl6_33 <=> sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.19/0.45  fof(f483,plain,(
% 0.19/0.45    r2_hidden(sK1,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_15 | ~spl6_32 | ~spl6_45)),
% 0.19/0.45    inference(subsumption_resolution,[],[f482,f73])).
% 0.19/0.45  fof(f73,plain,(
% 0.19/0.45    r2_hidden(sK1,sK3) | ~spl6_6),
% 0.19/0.45    inference(avatar_component_clause,[],[f72])).
% 0.19/0.45  fof(f72,plain,(
% 0.19/0.45    spl6_6 <=> r2_hidden(sK1,sK3)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.19/0.45  fof(f482,plain,(
% 0.19/0.45    ~r2_hidden(sK1,sK3) | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_15 | ~spl6_32 | ~spl6_45)),
% 0.19/0.45    inference(subsumption_resolution,[],[f481,f97])).
% 0.19/0.45  fof(f97,plain,(
% 0.19/0.45    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_12),
% 0.19/0.45    inference(avatar_component_clause,[],[f96])).
% 0.19/0.45  fof(f96,plain,(
% 0.19/0.45    spl6_12 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.19/0.45  fof(f481,plain,(
% 0.19/0.45    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK3) | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15 | ~spl6_32 | ~spl6_45)),
% 0.19/0.45    inference(subsumption_resolution,[],[f477,f323])).
% 0.19/0.45  fof(f323,plain,(
% 0.19/0.45    m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~spl6_32),
% 0.19/0.45    inference(avatar_component_clause,[],[f322])).
% 0.19/0.45  fof(f322,plain,(
% 0.19/0.45    spl6_32 <=> m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.19/0.45  fof(f477,plain,(
% 0.19/0.45    ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK3) | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4))) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15 | ~spl6_45)),
% 0.19/0.45    inference(resolution,[],[f464,f160])).
% 0.19/0.45  fof(f160,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r2_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK3) | r2_hidden(X0,k3_orders_2(sK0,sK3,X1))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f159,f53])).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    ~v2_struct_0(sK0) | spl6_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f52])).
% 0.19/0.45  fof(f52,plain,(
% 0.19/0.45    spl6_1 <=> v2_struct_0(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.19/0.45  fof(f159,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,sK3) | r2_hidden(X0,k3_orders_2(sK0,sK3,X1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f158,f69])).
% 0.19/0.45  fof(f69,plain,(
% 0.19/0.45    l1_orders_2(sK0) | ~spl6_5),
% 0.19/0.45    inference(avatar_component_clause,[],[f68])).
% 0.19/0.45  fof(f68,plain,(
% 0.19/0.45    spl6_5 <=> l1_orders_2(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.19/0.45  fof(f158,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,sK3) | r2_hidden(X0,k3_orders_2(sK0,sK3,X1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f157,f65])).
% 0.19/0.45  fof(f65,plain,(
% 0.19/0.45    v5_orders_2(sK0) | ~spl6_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f64])).
% 0.19/0.45  fof(f64,plain,(
% 0.19/0.45    spl6_4 <=> v5_orders_2(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.19/0.45  fof(f157,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,sK3) | r2_hidden(X0,k3_orders_2(sK0,sK3,X1))) ) | (~spl6_2 | ~spl6_3 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f156,f61])).
% 0.19/0.45  fof(f61,plain,(
% 0.19/0.45    v4_orders_2(sK0) | ~spl6_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f60])).
% 0.19/0.45  fof(f60,plain,(
% 0.19/0.45    spl6_3 <=> v4_orders_2(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.19/0.45  fof(f156,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,sK3) | r2_hidden(X0,k3_orders_2(sK0,sK3,X1))) ) | (~spl6_2 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f152,f57])).
% 0.19/0.45  fof(f57,plain,(
% 0.19/0.45    v3_orders_2(sK0) | ~spl6_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f56])).
% 0.19/0.45  fof(f56,plain,(
% 0.19/0.45    spl6_2 <=> v3_orders_2(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.19/0.45  fof(f152,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_orders_2(sK0,X0,X1) | ~r2_hidden(X0,sK3) | r2_hidden(X0,k3_orders_2(sK0,sK3,X1))) ) | ~spl6_15),
% 0.19/0.45    inference(resolution,[],[f126,f38])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,X3) | r2_hidden(X1,k3_orders_2(X0,X3,X2))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f12])).
% 0.19/0.45  fof(f12,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.45    inference(flattening,[],[f11])).
% 0.19/0.45  fof(f11,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.19/0.45  fof(f126,plain,(
% 0.19/0.45    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_15),
% 0.19/0.45    inference(avatar_component_clause,[],[f125])).
% 0.19/0.45  fof(f125,plain,(
% 0.19/0.45    spl6_15 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.19/0.45  fof(f464,plain,(
% 0.19/0.45    r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4)) | ~spl6_45),
% 0.19/0.45    inference(avatar_component_clause,[],[f463])).
% 0.19/0.45  fof(f463,plain,(
% 0.19/0.45    spl6_45 <=> r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.19/0.45  fof(f465,plain,(
% 0.19/0.45    spl6_45 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_32 | ~spl6_44),
% 0.19/0.45    inference(avatar_split_clause,[],[f446,f438,f322,f110,f96,f92,f68,f64,f60,f463])).
% 0.19/0.45  fof(f92,plain,(
% 0.19/0.45    spl6_11 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.19/0.45  fof(f110,plain,(
% 0.19/0.45    spl6_13 <=> r1_orders_2(sK0,sK1,sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.19/0.45  fof(f438,plain,(
% 0.19/0.45    spl6_44 <=> r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.19/0.45  fof(f446,plain,(
% 0.19/0.45    r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4)) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_32 | ~spl6_44)),
% 0.19/0.45    inference(subsumption_resolution,[],[f441,f323])).
% 0.19/0.45  fof(f441,plain,(
% 0.19/0.45    ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | r2_orders_2(sK0,sK1,sK5(sK0,sK3,sK4)) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13 | ~spl6_44)),
% 0.19/0.45    inference(resolution,[],[f439,f123])).
% 0.19/0.45  fof(f123,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_orders_2(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,sK1,X0)) ) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13)),
% 0.19/0.45    inference(subsumption_resolution,[],[f122,f61])).
% 0.19/0.45  fof(f122,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r2_orders_2(sK0,sK2,X0) | r2_orders_2(sK0,sK1,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_12 | ~spl6_13)),
% 0.19/0.45    inference(subsumption_resolution,[],[f121,f93])).
% 0.19/0.45  fof(f93,plain,(
% 0.19/0.45    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_11),
% 0.19/0.45    inference(avatar_component_clause,[],[f92])).
% 0.19/0.45  fof(f121,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r2_orders_2(sK0,sK2,X0) | r2_orders_2(sK0,sK1,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_12 | ~spl6_13)),
% 0.19/0.45    inference(subsumption_resolution,[],[f120,f97])).
% 0.19/0.45  fof(f120,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r2_orders_2(sK0,sK2,X0) | r2_orders_2(sK0,sK1,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_13)),
% 0.19/0.45    inference(subsumption_resolution,[],[f119,f69])).
% 0.19/0.45  fof(f119,plain,(
% 0.19/0.45    ( ! [X0] : (~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r2_orders_2(sK0,sK2,X0) | r2_orders_2(sK0,sK1,X0)) ) | (~spl6_4 | ~spl6_13)),
% 0.19/0.45    inference(subsumption_resolution,[],[f118,f65])).
% 0.19/0.45  fof(f118,plain,(
% 0.19/0.45    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~r2_orders_2(sK0,sK2,X0) | r2_orders_2(sK0,sK1,X0)) ) | ~spl6_13),
% 0.19/0.45    inference(resolution,[],[f111,f39])).
% 0.19/0.45  fof(f39,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X1,X2) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_orders_2(X0) | ~r2_orders_2(X0,X2,X3) | r2_orders_2(X0,X1,X3)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 0.19/0.45    inference(flattening,[],[f13])).
% 0.19/0.45  fof(f13,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_orders_2)).
% 0.19/0.45  fof(f111,plain,(
% 0.19/0.45    r1_orders_2(sK0,sK1,sK2) | ~spl6_13),
% 0.19/0.45    inference(avatar_component_clause,[],[f110])).
% 0.19/0.45  fof(f439,plain,(
% 0.19/0.45    r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4)) | ~spl6_44),
% 0.19/0.45    inference(avatar_component_clause,[],[f438])).
% 0.19/0.45  fof(f440,plain,(
% 0.19/0.45    spl6_44 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | ~spl6_15 | ~spl6_32 | ~spl6_33),
% 0.19/0.45    inference(avatar_split_clause,[],[f432,f356,f322,f125,f92,f76,f68,f64,f60,f56,f52,f438])).
% 0.19/0.45  fof(f76,plain,(
% 0.19/0.45    spl6_7 <=> r2_hidden(sK2,sK4)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.19/0.45  fof(f432,plain,(
% 0.19/0.45    r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_11 | ~spl6_15 | ~spl6_32 | ~spl6_33)),
% 0.19/0.45    inference(subsumption_resolution,[],[f429,f77])).
% 0.19/0.45  fof(f77,plain,(
% 0.19/0.45    r2_hidden(sK2,sK4) | ~spl6_7),
% 0.19/0.45    inference(avatar_component_clause,[],[f76])).
% 0.19/0.45  fof(f429,plain,(
% 0.19/0.45    ~r2_hidden(sK2,sK4) | r2_orders_2(sK0,sK2,sK5(sK0,sK3,sK4)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_15 | ~spl6_32 | ~spl6_33)),
% 0.19/0.45    inference(resolution,[],[f410,f93])).
% 0.19/0.45  fof(f410,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK4) | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4))) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15 | ~spl6_32 | ~spl6_33)),
% 0.19/0.45    inference(subsumption_resolution,[],[f409,f53])).
% 0.19/0.45  fof(f409,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15 | ~spl6_32 | ~spl6_33)),
% 0.19/0.45    inference(subsumption_resolution,[],[f408,f126])).
% 0.19/0.45  fof(f408,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_32 | ~spl6_33)),
% 0.19/0.45    inference(subsumption_resolution,[],[f407,f323])).
% 0.19/0.45  fof(f407,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_hidden(X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_33)),
% 0.19/0.45    inference(subsumption_resolution,[],[f406,f69])).
% 0.19/0.45  fof(f406,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_hidden(X0,sK4) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_33)),
% 0.19/0.45    inference(subsumption_resolution,[],[f405,f65])).
% 0.19/0.45  fof(f405,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_hidden(X0,sK4) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_33)),
% 0.19/0.45    inference(subsumption_resolution,[],[f404,f61])).
% 0.19/0.45  fof(f404,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_hidden(X0,sK4) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | (~spl6_2 | ~spl6_33)),
% 0.19/0.45    inference(subsumption_resolution,[],[f401,f57])).
% 0.19/0.45  fof(f401,plain,(
% 0.19/0.45    ( ! [X0] : (~r2_hidden(X0,sK4) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK5(sK0,sK3,sK4)) | v2_struct_0(sK0)) ) | ~spl6_33),
% 0.19/0.45    inference(superposition,[],[f36,f357])).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f12])).
% 0.19/0.45  fof(f394,plain,(
% 0.19/0.45    spl6_16 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_26 | ~spl6_28),
% 0.19/0.45    inference(avatar_split_clause,[],[f392,f263,f249,f114,f68,f64,f60,f56,f52,f177])).
% 0.19/0.45  fof(f177,plain,(
% 0.19/0.45    spl6_16 <=> k1_xboole_0 = sK4),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.19/0.45  fof(f114,plain,(
% 0.19/0.45    spl6_14 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.19/0.45  fof(f249,plain,(
% 0.19/0.45    spl6_26 <=> m1_orders_2(sK4,sK0,k1_xboole_0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.19/0.45  fof(f263,plain,(
% 0.19/0.45    spl6_28 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.19/0.45  fof(f392,plain,(
% 0.19/0.45    k1_xboole_0 = sK4 | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_26 | ~spl6_28)),
% 0.19/0.45    inference(subsumption_resolution,[],[f389,f250])).
% 0.19/0.45  fof(f250,plain,(
% 0.19/0.45    m1_orders_2(sK4,sK0,k1_xboole_0) | ~spl6_26),
% 0.19/0.45    inference(avatar_component_clause,[],[f249])).
% 0.19/0.45  fof(f389,plain,(
% 0.19/0.45    k1_xboole_0 = sK4 | ~m1_orders_2(sK4,sK0,k1_xboole_0) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_28)),
% 0.19/0.45    inference(resolution,[],[f349,f115])).
% 0.19/0.45  fof(f115,plain,(
% 0.19/0.45    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_14),
% 0.19/0.45    inference(avatar_component_clause,[],[f114])).
% 0.19/0.45  fof(f349,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,k1_xboole_0)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_28)),
% 0.19/0.45    inference(subsumption_resolution,[],[f348,f53])).
% 0.19/0.45  fof(f348,plain,(
% 0.19/0.45    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_28)),
% 0.19/0.45    inference(subsumption_resolution,[],[f347,f69])).
% 0.19/0.45  fof(f347,plain,(
% 0.19/0.45    ( ! [X0] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_28)),
% 0.19/0.45    inference(subsumption_resolution,[],[f346,f65])).
% 0.19/0.45  fof(f346,plain,(
% 0.19/0.45    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_3 | ~spl6_28)),
% 0.19/0.45    inference(subsumption_resolution,[],[f345,f61])).
% 0.19/0.45  fof(f345,plain,(
% 0.19/0.45    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,k1_xboole_0)) ) | (~spl6_2 | ~spl6_28)),
% 0.19/0.45    inference(subsumption_resolution,[],[f337,f57])).
% 0.19/0.45  fof(f337,plain,(
% 0.19/0.45    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | ~m1_orders_2(X0,sK0,k1_xboole_0)) ) | ~spl6_28),
% 0.19/0.45    inference(resolution,[],[f264,f44])).
% 0.19/0.45  fof(f44,plain,(
% 0.19/0.45    ( ! [X2,X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,k1_xboole_0)) )),
% 0.19/0.45    inference(equality_resolution,[],[f35])).
% 0.19/0.45  fof(f35,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != X1 | k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.45    inference(flattening,[],[f9])).
% 0.19/0.45  fof(f9,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).
% 0.19/0.45  fof(f264,plain,(
% 0.19/0.45    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_28),
% 0.19/0.45    inference(avatar_component_clause,[],[f263])).
% 0.19/0.45  fof(f358,plain,(
% 0.19/0.45    spl6_33 | ~spl6_10 | ~spl6_14 | ~spl6_30),
% 0.19/0.45    inference(avatar_split_clause,[],[f318,f273,f114,f88,f356])).
% 0.19/0.45  fof(f88,plain,(
% 0.19/0.45    spl6_10 <=> m1_orders_2(sK4,sK0,sK3)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.19/0.45  fof(f273,plain,(
% 0.19/0.45    spl6_30 <=> ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X4,sK0,sK3) | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.19/0.45  fof(f318,plain,(
% 0.19/0.45    sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) | (~spl6_10 | ~spl6_14 | ~spl6_30)),
% 0.19/0.45    inference(subsumption_resolution,[],[f316,f89])).
% 0.19/0.45  fof(f89,plain,(
% 0.19/0.45    m1_orders_2(sK4,sK0,sK3) | ~spl6_10),
% 0.19/0.45    inference(avatar_component_clause,[],[f88])).
% 0.19/0.45  fof(f316,plain,(
% 0.19/0.45    ~m1_orders_2(sK4,sK0,sK3) | sK4 = k3_orders_2(sK0,sK3,sK5(sK0,sK3,sK4)) | (~spl6_14 | ~spl6_30)),
% 0.19/0.45    inference(resolution,[],[f274,f115])).
% 0.19/0.45  fof(f274,plain,(
% 0.19/0.45    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X4,sK0,sK3) | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4) ) | ~spl6_30),
% 0.19/0.45    inference(avatar_component_clause,[],[f273])).
% 0.19/0.45  fof(f324,plain,(
% 0.19/0.45    spl6_32 | ~spl6_10 | ~spl6_14 | ~spl6_25),
% 0.19/0.45    inference(avatar_split_clause,[],[f254,f233,f114,f88,f322])).
% 0.19/0.45  fof(f233,plain,(
% 0.19/0.45    spl6_25 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X2,sK0,sK3) | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.19/0.45  fof(f254,plain,(
% 0.19/0.45    m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | (~spl6_10 | ~spl6_14 | ~spl6_25)),
% 0.19/0.45    inference(subsumption_resolution,[],[f252,f89])).
% 0.19/0.45  fof(f252,plain,(
% 0.19/0.45    ~m1_orders_2(sK4,sK0,sK3) | m1_subset_1(sK5(sK0,sK3,sK4),u1_struct_0(sK0)) | (~spl6_14 | ~spl6_25)),
% 0.19/0.45    inference(resolution,[],[f234,f115])).
% 0.19/0.45  fof(f234,plain,(
% 0.19/0.45    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X2,sK0,sK3) | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0))) ) | ~spl6_25),
% 0.19/0.45    inference(avatar_component_clause,[],[f233])).
% 0.19/0.45  fof(f275,plain,(
% 0.19/0.45    spl6_20 | spl6_30 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15),
% 0.19/0.45    inference(avatar_split_clause,[],[f175,f125,f68,f64,f60,f56,f52,f273,f193])).
% 0.19/0.45  fof(f193,plain,(
% 0.19/0.45    spl6_20 <=> k1_xboole_0 = sK3),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.19/0.45  fof(f175,plain,(
% 0.19/0.45    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4 | ~m1_orders_2(X4,sK0,sK3)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f174,f53])).
% 0.19/0.45  fof(f174,plain,(
% 0.19/0.45    ( ! [X4] : (v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4 | ~m1_orders_2(X4,sK0,sK3)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f173,f69])).
% 0.19/0.45  fof(f173,plain,(
% 0.19/0.45    ( ! [X4] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4 | ~m1_orders_2(X4,sK0,sK3)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f172,f65])).
% 0.19/0.45  fof(f172,plain,(
% 0.19/0.45    ( ! [X4] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4 | ~m1_orders_2(X4,sK0,sK3)) ) | (~spl6_2 | ~spl6_3 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f171,f61])).
% 0.19/0.45  fof(f171,plain,(
% 0.19/0.45    ( ! [X4] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4 | ~m1_orders_2(X4,sK0,sK3)) ) | (~spl6_2 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f155,f57])).
% 0.19/0.45  fof(f155,plain,(
% 0.19/0.45    ( ! [X4] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | k3_orders_2(sK0,sK3,sK5(sK0,sK3,X4)) = X4 | ~m1_orders_2(X4,sK0,sK3)) ) | ~spl6_15),
% 0.19/0.45    inference(resolution,[],[f126,f32])).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK5(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f265,plain,(
% 0.19/0.45    spl6_28 | ~spl6_15 | ~spl6_20),
% 0.19/0.45    inference(avatar_split_clause,[],[f199,f193,f125,f263])).
% 0.19/0.45  fof(f199,plain,(
% 0.19/0.45    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl6_15 | ~spl6_20)),
% 0.19/0.45    inference(superposition,[],[f126,f194])).
% 0.19/0.45  fof(f194,plain,(
% 0.19/0.45    k1_xboole_0 = sK3 | ~spl6_20),
% 0.19/0.45    inference(avatar_component_clause,[],[f193])).
% 0.19/0.45  fof(f251,plain,(
% 0.19/0.45    spl6_26 | ~spl6_10 | ~spl6_20),
% 0.19/0.45    inference(avatar_split_clause,[],[f200,f193,f88,f249])).
% 0.19/0.45  fof(f200,plain,(
% 0.19/0.45    m1_orders_2(sK4,sK0,k1_xboole_0) | (~spl6_10 | ~spl6_20)),
% 0.19/0.45    inference(superposition,[],[f89,f194])).
% 0.19/0.45  fof(f235,plain,(
% 0.19/0.45    spl6_20 | spl6_25 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15),
% 0.19/0.45    inference(avatar_split_clause,[],[f165,f125,f68,f64,f60,f56,f52,f233,f193])).
% 0.19/0.45  fof(f165,plain,(
% 0.19/0.45    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0)) | ~m1_orders_2(X2,sK0,sK3)) ) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f164,f53])).
% 0.19/0.45  fof(f164,plain,(
% 0.19/0.45    ( ! [X2] : (v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0)) | ~m1_orders_2(X2,sK0,sK3)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f163,f69])).
% 0.19/0.45  fof(f163,plain,(
% 0.19/0.45    ( ! [X2] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0)) | ~m1_orders_2(X2,sK0,sK3)) ) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f162,f65])).
% 0.19/0.45  fof(f162,plain,(
% 0.19/0.45    ( ! [X2] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0)) | ~m1_orders_2(X2,sK0,sK3)) ) | (~spl6_2 | ~spl6_3 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f161,f61])).
% 0.19/0.45  fof(f161,plain,(
% 0.19/0.45    ( ! [X2] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0)) | ~m1_orders_2(X2,sK0,sK3)) ) | (~spl6_2 | ~spl6_15)),
% 0.19/0.45    inference(subsumption_resolution,[],[f153,f57])).
% 0.19/0.45  fof(f153,plain,(
% 0.19/0.45    ( ! [X2] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3 | m1_subset_1(sK5(sK0,sK3,X2),u1_struct_0(sK0)) | ~m1_orders_2(X2,sK0,sK3)) ) | ~spl6_15),
% 0.19/0.45    inference(resolution,[],[f126,f30])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f206,plain,(
% 0.19/0.45    k1_xboole_0 != sK3 | k1_xboole_0 != sK4 | r2_hidden(sK1,sK4) | ~r2_hidden(sK1,sK3)),
% 0.19/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.45  fof(f127,plain,(
% 0.19/0.45    spl6_15),
% 0.19/0.45    inference(avatar_split_clause,[],[f22,f125])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f8,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r2_hidden(X1,X4) & m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.19/0.45    inference(flattening,[],[f7])).
% 0.19/0.45  fof(f7,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r2_hidden(X1,X4) & (m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,negated_conjecture,(
% 0.19/0.45    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 0.19/0.45    inference(negated_conjecture,[],[f5])).
% 0.19/0.45  fof(f5,conjecture,(
% 0.19/0.45    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ! [X4] : (m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_orders_2(X4,X0,X3) & r2_hidden(X2,X4) & r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) => r2_hidden(X1,X4)))))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_orders_2)).
% 0.19/0.45  fof(f116,plain,(
% 0.19/0.45    spl6_14),
% 0.19/0.45    inference(avatar_split_clause,[],[f16,f114])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f112,plain,(
% 0.19/0.45    spl6_13 | ~spl6_5 | ~spl6_9 | ~spl6_11 | ~spl6_12),
% 0.19/0.45    inference(avatar_split_clause,[],[f103,f96,f92,f84,f68,f110])).
% 0.19/0.45  fof(f84,plain,(
% 0.19/0.45    spl6_9 <=> r2_orders_2(sK0,sK1,sK2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.19/0.45  fof(f103,plain,(
% 0.19/0.45    r1_orders_2(sK0,sK1,sK2) | (~spl6_5 | ~spl6_9 | ~spl6_11 | ~spl6_12)),
% 0.19/0.45    inference(subsumption_resolution,[],[f102,f69])).
% 0.19/0.45  fof(f102,plain,(
% 0.19/0.45    r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | (~spl6_9 | ~spl6_11 | ~spl6_12)),
% 0.19/0.45    inference(subsumption_resolution,[],[f101,f93])).
% 0.19/0.45  fof(f101,plain,(
% 0.19/0.45    ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | (~spl6_9 | ~spl6_12)),
% 0.19/0.45    inference(subsumption_resolution,[],[f99,f97])).
% 0.19/0.45  fof(f99,plain,(
% 0.19/0.45    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~spl6_9),
% 0.19/0.45    inference(resolution,[],[f85,f41])).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~l1_orders_2(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.19/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.19/0.45  fof(f85,plain,(
% 0.19/0.45    r2_orders_2(sK0,sK1,sK2) | ~spl6_9),
% 0.19/0.45    inference(avatar_component_clause,[],[f84])).
% 0.19/0.45  fof(f98,plain,(
% 0.19/0.45    spl6_12),
% 0.19/0.45    inference(avatar_split_clause,[],[f24,f96])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f94,plain,(
% 0.19/0.45    spl6_11),
% 0.19/0.45    inference(avatar_split_clause,[],[f23,f92])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f90,plain,(
% 0.19/0.45    spl6_10),
% 0.19/0.45    inference(avatar_split_clause,[],[f20,f88])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    m1_orders_2(sK4,sK0,sK3)),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f86,plain,(
% 0.19/0.45    spl6_9),
% 0.19/0.45    inference(avatar_split_clause,[],[f17,f84])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    r2_orders_2(sK0,sK1,sK2)),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f82,plain,(
% 0.19/0.45    ~spl6_8),
% 0.19/0.45    inference(avatar_split_clause,[],[f21,f80])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ~r2_hidden(sK1,sK4)),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f78,plain,(
% 0.19/0.45    spl6_7),
% 0.19/0.45    inference(avatar_split_clause,[],[f19,f76])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    r2_hidden(sK2,sK4)),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f74,plain,(
% 0.19/0.45    spl6_6),
% 0.19/0.45    inference(avatar_split_clause,[],[f18,f72])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    r2_hidden(sK1,sK3)),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f70,plain,(
% 0.19/0.45    spl6_5),
% 0.19/0.45    inference(avatar_split_clause,[],[f29,f68])).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    l1_orders_2(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f66,plain,(
% 0.19/0.45    spl6_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f28,f64])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    v5_orders_2(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f62,plain,(
% 0.19/0.45    spl6_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f27,f60])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    v4_orders_2(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f58,plain,(
% 0.19/0.45    spl6_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f26,f56])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    v3_orders_2(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f54,plain,(
% 0.19/0.45    ~spl6_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f25,f52])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ~v2_struct_0(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (24505)------------------------------
% 0.19/0.45  % (24505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (24505)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (24505)Memory used [KB]: 6396
% 0.19/0.45  % (24505)Time elapsed: 0.074 s
% 0.19/0.45  % (24505)------------------------------
% 0.19/0.45  % (24505)------------------------------
% 0.19/0.46  % (24498)Success in time 0.117 s
%------------------------------------------------------------------------------
