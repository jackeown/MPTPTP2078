%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1457+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:56 EST 2020

% Result     : Theorem 2.54s
% Output     : Refutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  252 (3044 expanded)
%              Number of leaves         :   43 (1215 expanded)
%              Depth                    :   17
%              Number of atoms          : 1552 (11531 expanded)
%              Number of equality atoms :  146 (1064 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1671,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f90,f95,f100,f105,f110,f119,f128,f141,f156,f219,f224,f229,f234,f239,f281,f286,f701,f702,f707,f712,f717,f722,f727,f732,f737,f742,f1602,f1624,f1665,f1670])).

fof(f1670,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_13
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f1669])).

fof(f1669,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_13
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f1668,f1622])).

fof(f1622,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1621,f408])).

fof(f408,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f383,f406])).

fof(f406,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f405,f131])).

fof(f131,plain,
    ( sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f94,f89,f99,f84,f104,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(f104,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f84,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f99,plain,
    ( l3_lattices(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f89,plain,
    ( v10_lattices(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f94,plain,
    ( v17_lattices(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_3
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f405,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f404,f398])).

fof(f398,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f397,f131])).

fof(f397,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))) = k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f304,f361])).

fof(f361,plain,
    ( k4_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f341,f158])).

fof(f158,plain,
    ( k4_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f94,f84,f89,f99,f109,f104,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_filter_0(X0,X1,X2) = k3_lattices(X0,k7_lattices(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_filter_0(X0,X1,X2) = k3_lattices(X0,k7_lattices(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_filter_0(X0,X1,X2) = k3_lattices(X0,k7_lattices(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k4_filter_0(X0,X1,X2) = k3_lattices(X0,k7_lattices(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_filter_0)).

fof(f109,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f341,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f84,f140,f127,f109,f280,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f280,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl3_19
  <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f127,plain,
    ( l2_lattices(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_8
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f140,plain,
    ( v4_lattices(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl3_9
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f304,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))) = k7_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f89,f94,f84,f99,f109,f280,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_lattices)).

fof(f404,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f301,f158])).

fof(f301,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f89,f84,f94,f99,f109,f280,f70])).

fof(f383,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f310,f131])).

fof(f310,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f89,f94,f84,f99,f109,f280,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k7_filter_0(X0,X1,X2) = k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_filter_0(X0,X1,X2) = k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_filter_0(X0,X1,X2) = k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_filter_0(X0,X1,X2) = k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_filter_1)).

fof(f1621,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1620,f167])).

fof(f167,plain,
    ( k7_filter_0(sK0,sK1,sK2) = k4_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK2,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f89,f99,f84,f104,f109,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_filter_0)).

fof(f1620,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK2,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1619,f620])).

fof(f620,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f619,f329])).

fof(f329,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | spl3_1
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f223,f118,f84,f109,f280,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f118,plain,
    ( l1_lattices(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_7
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f223,plain,
    ( v6_lattices(sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl3_15
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f619,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f618,f132])).

fof(f132,plain,
    ( sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f94,f89,f99,f84,f109,f67])).

fof(f618,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f473,f424])).

fof(f424,plain,
    ( k4_filter_0(sK0,sK1,sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f423,f417])).

fof(f417,plain,
    ( k4_filter_0(sK0,sK1,sK2) = k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f416,f159])).

fof(f159,plain,
    ( k4_filter_0(sK0,sK1,sK2) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f94,f84,f89,f99,f104,f109,f68])).

fof(f416,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f298,f131])).

fof(f298,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f89,f94,f84,f99,f109,f280,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattices)).

fof(f423,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f422,f329])).

fof(f422,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f295,f131])).

fof(f295,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f89,f84,f94,f99,f109,f280,f69])).

fof(f473,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1))) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f89,f94,f84,f99,f104,f285,f70])).

fof(f285,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl3_20
  <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f1619,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK2,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1319,f407])).

fof(f407,plain,
    ( k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f398,f406])).

fof(f1319,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK2,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)),k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(unit_resulting_resolution,[],[f89,f84,f94,f99,f716,f721,f69])).

fof(f721,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f719])).

fof(f719,plain,
    ( spl3_25
  <=> m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f716,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f714])).

fof(f714,plain,
    ( spl3_24
  <=> m1_subset_1(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1668,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_13
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1667,f408])).

fof(f1667,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_13
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f214,f406])).

fof(f214,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK2))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl3_13
  <=> k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1665,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | spl3_14
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f1664])).

fof(f1664,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | spl3_14
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f218,f620])).

fof(f218,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl3_14
  <=> k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1624,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_12
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f1623])).

fof(f1623,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_12
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f1622,f210])).

fof(f210,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl3_12
  <=> k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1602,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_12
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f1601])).

fof(f1601,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_12
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f1600,f210])).

fof(f1600,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1599,f694])).

fof(f694,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f589,f691])).

fof(f691,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f688,f446])).

fof(f446,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)),k3_lattices(sK0,sK1,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f316,f444])).

fof(f444,plain,
    ( k3_lattices(sK0,sK1,sK2) = k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f443,f249])).

fof(f249,plain,
    ( k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2)
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f84,f127,f104,f109,f140,f77])).

fof(f443,plain,
    ( k3_lattices(sK0,sK2,sK1) = k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f289,f131])).

fof(f289,plain,
    ( k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f89,f84,f94,f99,f109,f280,f68])).

fof(f316,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)),k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f84,f89,f99,f109,f280,f72])).

fof(f688,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)),k3_lattices(sK0,sK1,sK2)) = k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f669,f687])).

fof(f687,plain,
    ( k3_lattices(sK0,sK1,sK2) = k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f453,f132])).

fof(f453,plain,
    ( k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK2)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f89,f84,f94,f99,f104,f285,f68])).

fof(f669,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)),k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f489,f667])).

fof(f667,plain,
    ( k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k4_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f457,f436])).

fof(f436,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f273,f435])).

fof(f435,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK1,sK2)) = k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f174,f292])).

fof(f292,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f89,f94,f84,f99,f109,f280,f68])).

fof(f174,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f94,f84,f89,f99,f104,f109,f69])).

fof(f273,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_lattices(sK0,sK1,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f173,f265])).

fof(f265,plain,
    ( k4_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK1,sK2)
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f118,f84,f104,f109,f223,f75])).

fof(f173,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,sK2,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f94,f84,f89,f99,f109,f104,f69])).

fof(f457,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k4_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f89,f94,f84,f99,f104,f285,f68])).

fof(f489,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k4_filter_0(sK0,sK2,k7_lattices(sK0,sK1)),k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f84,f89,f99,f104,f285,f72])).

fof(f589,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f588,f329])).

fof(f588,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK2),sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f481,f132])).

fof(f481,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1))))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f89,f94,f84,f99,f104,f285,f71])).

fof(f1599,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1598,f275])).

fof(f275,plain,
    ( k7_filter_0(sK0,sK1,sK2) = k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f166,f274])).

fof(f274,plain,
    ( k7_filter_0(sK0,sK1,sK2) = k7_filter_0(sK0,sK2,sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f272,f197])).

fof(f197,plain,
    ( k7_filter_0(sK0,sK1,sK2) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f193,f185])).

fof(f185,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,sK1,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f94,f84,f89,f99,f104,f109,f70])).

fof(f193,plain,
    ( k7_filter_0(sK0,sK1,sK2) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f94,f84,f89,f99,f104,f109,f71])).

fof(f272,plain,
    ( k7_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f261,f265])).

fof(f261,plain,
    ( k7_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f198,f249])).

fof(f198,plain,
    ( k7_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f192,f184])).

fof(f184,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f94,f84,f89,f99,f109,f104,f70])).

fof(f192,plain,
    ( k7_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f94,f84,f89,f99,f109,f104,f71])).

fof(f166,plain,
    ( k7_filter_0(sK0,sK2,sK1) = k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f89,f99,f84,f109,f104,f72])).

fof(f1598,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1597,f407])).

fof(f1597,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2))) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1326,f620])).

fof(f1326,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2))) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)),k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(unit_resulting_resolution,[],[f89,f94,f84,f99,f716,f721,f69])).

fof(f742,plain,
    ( spl3_29
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f149,f107,f97,f87,f82,f739])).

fof(f739,plain,
    ( spl3_29
  <=> m1_subset_1(k7_filter_0(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f149,plain,
    ( m1_subset_1(k7_filter_0(sK0,sK1,sK1),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f84,f99,f89,f109,f109,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_filter_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_filter_0)).

fof(f737,plain,
    ( spl3_28
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f148,f107,f102,f97,f87,f82,f734])).

fof(f734,plain,
    ( spl3_28
  <=> m1_subset_1(k7_filter_0(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f148,plain,
    ( m1_subset_1(k7_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f84,f99,f89,f104,f109,f80])).

fof(f732,plain,
    ( spl3_27
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f146,f102,f97,f87,f82,f729])).

fof(f729,plain,
    ( spl3_27
  <=> m1_subset_1(k7_filter_0(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f146,plain,
    ( m1_subset_1(k7_filter_0(sK0,sK2,sK2),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f84,f99,f89,f104,f104,f80])).

fof(f727,plain,
    ( spl3_26
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f145,f107,f97,f87,f82,f724])).

fof(f724,plain,
    ( spl3_26
  <=> m1_subset_1(k4_filter_0(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f145,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK1,sK1),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f84,f99,f89,f109,f109,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_filter_0)).

fof(f722,plain,
    ( spl3_25
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f144,f107,f102,f97,f87,f82,f719])).

fof(f144,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f84,f99,f89,f104,f109,f79])).

fof(f717,plain,
    ( spl3_24
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f143,f107,f102,f97,f87,f82,f714])).

fof(f143,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f84,f99,f89,f109,f104,f79])).

fof(f712,plain,
    ( spl3_23
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f142,f102,f97,f87,f82,f709])).

fof(f709,plain,
    ( spl3_23
  <=> m1_subset_1(k4_filter_0(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f142,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK2,sK2),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f84,f99,f89,f104,f104,f79])).

fof(f707,plain,
    ( spl3_22
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f132,f107,f97,f92,f87,f82,f704])).

fof(f704,plain,
    ( spl3_22
  <=> sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f702,plain,
    ( ~ spl3_12
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_11
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f692,f283,f278,f221,f204,f138,f125,f116,f107,f102,f97,f92,f87,f82,f208])).

fof(f204,plain,
    ( spl3_11
  <=> k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f692,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_11
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f608,f691])).

fof(f608,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | spl3_11
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f206,f605])).

fof(f605,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f604,f589])).

fof(f604,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f603,f406])).

fof(f603,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK2),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f477,f132])).

fof(f477,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK2),k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f89,f84,f94,f99,f104,f285,f71])).

fof(f206,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f204])).

fof(f701,plain,
    ( spl3_21
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f131,f102,f97,f92,f87,f82,f698])).

fof(f698,plain,
    ( spl3_21
  <=> sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f286,plain,
    ( spl3_20
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f130,f107,f97,f82,f283])).

fof(f130,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f84,f99,f109,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f281,plain,
    ( spl3_19
    | spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f129,f102,f97,f82,f278])).

fof(f129,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f84,f99,f104,f73])).

fof(f239,plain,
    ( spl3_18
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f123,f97,f87,f82,f236])).

fof(f236,plain,
    ( spl3_18
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f123,plain,
    ( v9_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f99,f89,f84,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f234,plain,
    ( spl3_17
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f122,f97,f87,f82,f231])).

fof(f231,plain,
    ( spl3_17
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f122,plain,
    ( v8_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f99,f89,f84,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f229,plain,
    ( spl3_16
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f121,f97,f87,f82,f226])).

fof(f226,plain,
    ( spl3_16
  <=> v7_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f121,plain,
    ( v7_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f99,f89,f84,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f224,plain,
    ( spl3_15
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f120,f97,f87,f82,f221])).

fof(f120,plain,
    ( v6_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f99,f89,f84,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f219,plain,
    ( ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f52,f216,f212,f208,f204])).

fof(f52,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK2))
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,k7_lattices(X0,X1),X2)
                | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,X1,k7_lattices(X0,X2))
                | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,X1),X2))
                | k7_lattices(X0,k4_filter_0(X0,X1,X2)) != k4_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,k7_lattices(X0,X1),X2)
                | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k7_filter_0(X0,X1,k7_lattices(X0,X2))
                | k7_lattices(X0,k7_filter_0(X0,X1,X2)) != k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,X1),X2))
                | k7_lattices(X0,k4_filter_0(X0,X1,X2)) != k4_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k7_filter_0(X0,k7_lattices(X0,X1),X2)
                  & k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k7_filter_0(X0,X1,k7_lattices(X0,X2))
                  & k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,X1),X2))
                  & k7_lattices(X0,k4_filter_0(X0,X1,X2)) = k4_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k7_filter_0(X0,k7_lattices(X0,X1),X2)
                & k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k7_filter_0(X0,X1,k7_lattices(X0,X2))
                & k7_lattices(X0,k7_filter_0(X0,X1,X2)) = k3_lattices(X0,k4_lattices(X0,X1,k7_lattices(X0,X2)),k4_lattices(X0,k7_lattices(X0,X1),X2))
                & k7_lattices(X0,k4_filter_0(X0,X1,X2)) = k4_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_filter_1)).

fof(f156,plain,
    ( spl3_10
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f114,f97,f87,f82,f153])).

fof(f153,plain,
    ( spl3_10
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f114,plain,
    ( v5_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f99,f89,f84,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f141,plain,
    ( spl3_9
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f113,f97,f87,f82,f138])).

fof(f113,plain,
    ( v4_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f99,f89,f84,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f128,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f112,f97,f125])).

fof(f112,plain,
    ( l2_lattices(sK0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f99,f60])).

fof(f60,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f119,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f111,f97,f116])).

fof(f111,plain,
    ( l1_lattices(sK0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f99,f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f110,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f54,f107])).

fof(f54,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f105,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f53,f102])).

fof(f53,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f100,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f58,f97])).

fof(f58,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f95,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f57,f92])).

fof(f57,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f90,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f56,f87])).

fof(f56,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f85,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f55,f82])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

%------------------------------------------------------------------------------
