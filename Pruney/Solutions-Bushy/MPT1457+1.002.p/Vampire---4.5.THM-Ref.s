%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1457+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:56 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  235 (2850 expanded)
%              Number of leaves         :   38 (1131 expanded)
%              Depth                    :   19
%              Number of atoms          : 1443 (10792 expanded)
%              Number of equality atoms :  144 (1016 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f98,f107,f116,f129,f154,f199,f204,f209,f214,f219,f242,f247,f599,f604,f609,f614,f619,f624,f629,f1246,f1261,f1294,f1299])).

fof(f1299,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_13
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f1298])).

fof(f1298,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_13
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f1297,f1259])).

fof(f1259,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1258,f337])).

fof(f337,plain,
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
    inference(backward_demodulation,[],[f319,f335])).

fof(f335,plain,
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
    inference(forward_demodulation,[],[f334,f119])).

fof(f119,plain,
    ( sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f82,f77,f87,f72,f92,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_lattices)).

fof(f92,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f72,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f87,plain,
    ( l3_lattices(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f77,plain,
    ( v10_lattices(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f82,plain,
    ( v17_lattices(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_3
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f334,plain,
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
    inference(forward_demodulation,[],[f333,f328])).

fof(f328,plain,
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
    inference(forward_demodulation,[],[f327,f119])).

fof(f327,plain,
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
    inference(forward_demodulation,[],[f265,f304])).

fof(f304,plain,
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
    inference(forward_demodulation,[],[f296,f136])).

fof(f136,plain,
    ( k4_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f82,f72,f77,f87,f97,f92,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_filter_0(X0,X1,X2) = k3_lattices(X0,k7_lattices(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
             => k4_filter_0(X0,X1,X2) = k3_lattices(X0,k7_lattices(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_filter_0)).

fof(f97,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f296,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f128,f115,f72,f97,f241,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f241,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl3_19
  <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f115,plain,
    ( l2_lattices(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_8
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f128,plain,
    ( v4_lattices(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_9
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f265,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))) = k7_lattices(sK0,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f77,f82,f72,f87,f97,f241,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) = k7_lattices(X0,k3_lattices(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_lattices)).

fof(f333,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f262,f136])).

fof(f262,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f77,f72,f82,f87,f97,f241,f61])).

fof(f319,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f271,f119])).

fof(f271,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,k7_lattices(sK0,sK2))))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f77,f82,f72,f87,f97,f241,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k7_filter_0(X0,X1,X2) = k3_lattices(X0,k4_lattices(X0,X1,X2),k4_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_filter_1)).

fof(f1258,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1257,f145])).

fof(f145,plain,
    ( k7_filter_0(sK0,sK1,sK2) = k4_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK2,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f77,f87,f72,f92,f97,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k7_filter_0(X0,X1,X2) = k4_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_filter_0)).

fof(f1257,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k7_lattices(sK0,sK1))) = k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK2,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1256,f525])).

fof(f525,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f524,f120])).

fof(f120,plain,
    ( sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f82,f77,f87,f72,f97,f58])).

fof(f524,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f397,f137])).

fof(f137,plain,
    ( k4_filter_0(sK0,sK1,sK2) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK2)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f82,f72,f77,f87,f92,f97,f59])).

fof(f397,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f77,f72,f82,f87,f92,f246,f61])).

fof(f246,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl3_20
  <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f1256,plain,
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
    inference(forward_demodulation,[],[f1046,f336])).

fof(f336,plain,
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
    inference(backward_demodulation,[],[f328,f335])).

fof(f1046,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK2,sK1))) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)),k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(unit_resulting_resolution,[],[f77,f72,f82,f87,f618,f623,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k7_lattices(X0,k4_lattices(X0,X1,X2)) = k3_lattices(X0,k7_lattices(X0,X1),k7_lattices(X0,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattices)).

fof(f623,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f621])).

fof(f621,plain,
    ( spl3_25
  <=> m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f618,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f616])).

fof(f616,plain,
    ( spl3_24
  <=> m1_subset_1(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f1297,plain,
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
    inference(forward_demodulation,[],[f1296,f337])).

fof(f1296,plain,
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
    inference(forward_demodulation,[],[f194,f335])).

fof(f194,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK2))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl3_13
  <=> k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1294,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_14
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f1293])).

fof(f1293,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | spl3_14
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f198,f525])).

fof(f198,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl3_14
  <=> k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1261,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_12
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f1260])).

fof(f1260,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_12
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f1259,f190])).

fof(f190,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl3_12
  <=> k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1246,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_12
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(avatar_contradiction_clause,[],[f1245])).

fof(f1245,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_12
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f1244,f190])).

fof(f1244,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1243,f597])).

fof(f597,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
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
    inference(backward_demodulation,[],[f527,f594])).

fof(f594,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
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
    inference(forward_demodulation,[],[f591,f374])).

fof(f374,plain,
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
    inference(backward_demodulation,[],[f277,f372])).

fof(f372,plain,
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
    inference(forward_demodulation,[],[f371,f225])).

fof(f225,plain,
    ( k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2)
    | spl3_1
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f115,f72,f92,f97,f128,f67])).

fof(f371,plain,
    ( k3_lattices(sK0,sK2,sK1) = k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f250,f119])).

fof(f250,plain,
    ( k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f77,f72,f82,f87,f97,f241,f59])).

fof(f277,plain,
    ( k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)),k4_filter_0(sK0,k7_lattices(sK0,sK2),sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f72,f77,f87,f97,f241,f63])).

fof(f591,plain,
    ( k4_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)),k3_lattices(sK0,sK1,sK2)) = k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
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
    inference(backward_demodulation,[],[f573,f590])).

fof(f590,plain,
    ( k3_lattices(sK0,sK1,sK2) = k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f381,f120])).

fof(f381,plain,
    ( k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK2)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f77,f72,f82,f87,f92,f246,f59])).

fof(f573,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)),k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2))
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
    inference(backward_demodulation,[],[f417,f571])).

fof(f571,plain,
    ( k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)) = k4_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
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
    inference(forward_demodulation,[],[f385,f454])).

fof(f454,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f444,f253])).

fof(f253,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f77,f82,f72,f87,f97,f241,f59])).

fof(f444,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f128,f115,f72,f241,f246,f67])).

fof(f385,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k4_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f77,f82,f72,f87,f92,f246,f59])).

fof(f417,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k4_filter_0(sK0,sK2,k7_lattices(sK0,sK1)),k4_filter_0(sK0,k7_lattices(sK0,sK1),sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f72,f77,f87,f92,f246,f63])).

fof(f527,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f482,f526])).

fof(f526,plain,
    ( k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f499,f525])).

fof(f499,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f498,f120])).

fof(f498,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f401,f457])).

fof(f457,plain,
    ( k4_filter_0(sK0,sK1,sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f442,f137])).

fof(f442,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f128,f115,f72,f92,f246,f67])).

fof(f401,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1))) = k7_lattices(sK0,k3_lattices(sK0,sK2,k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f77,f82,f72,f87,f92,f246,f61])).

fof(f482,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK2),sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f409,f120])).

fof(f409,plain,
    ( k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,k7_lattices(sK0,sK1))))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f77,f82,f72,f87,f92,f246,f62])).

fof(f1243,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1242,f514])).

fof(f514,plain,
    ( k7_filter_0(sK0,sK1,sK2) = k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2))
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
    inference(backward_demodulation,[],[f144,f513])).

fof(f513,plain,
    ( k7_filter_0(sK0,sK1,sK2) = k7_filter_0(sK0,sK2,sK1)
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
    inference(forward_demodulation,[],[f510,f177])).

fof(f177,plain,
    ( k7_filter_0(sK0,sK1,sK2) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f173,f165])).

fof(f165,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k7_lattices(sK0,k3_lattices(sK0,sK1,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f82,f72,f77,f87,f92,f97,f61])).

fof(f173,plain,
    ( k7_filter_0(sK0,sK1,sK2) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k4_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f82,f72,f77,f87,f92,f97,f62])).

fof(f510,plain,
    ( k7_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)))
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
    inference(backward_demodulation,[],[f232,f505])).

fof(f505,plain,
    ( k4_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK1,sK2)
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
    inference(forward_demodulation,[],[f504,f120])).

fof(f504,plain,
    ( k4_lattices(sK0,sK2,sK1) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),sK2)
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
    inference(forward_demodulation,[],[f503,f119])).

fof(f503,plain,
    ( k4_lattices(sK0,sK2,sK1) = k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2)))
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
    inference(forward_demodulation,[],[f502,f495])).

fof(f495,plain,
    ( k4_lattices(sK0,sK2,sK1) = k7_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)))
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
    inference(forward_demodulation,[],[f494,f119])).

fof(f494,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),sK1) = k7_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f493,f120])).

fof(f493,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,k7_lattices(sK0,sK1))) = k7_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f403,f454])).

fof(f403,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK2)),k7_lattices(sK0,k7_lattices(sK0,sK1))) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f77,f82,f72,f87,f241,f246,f61])).

fof(f502,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))) = k7_lattices(sK0,k4_filter_0(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f399,f253])).

fof(f399,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,k7_lattices(sK0,sK2))) = k7_lattices(sK0,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f77,f72,f82,f87,f241,f246,f61])).

fof(f232,plain,
    ( k7_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),k7_lattices(sK0,k3_lattices(sK0,sK1,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f178,f225])).

fof(f178,plain,
    ( k7_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),k7_lattices(sK0,k3_lattices(sK0,sK2,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f172,f164])).

fof(f164,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k7_lattices(sK0,k3_lattices(sK0,sK2,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f82,f72,f77,f87,f97,f92,f61])).

fof(f172,plain,
    ( k7_filter_0(sK0,sK2,sK1) = k3_lattices(sK0,k4_lattices(sK0,sK2,sK1),k4_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f82,f72,f77,f87,f97,f92,f62])).

fof(f144,plain,
    ( k7_filter_0(sK0,sK2,sK1) = k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f77,f87,f72,f97,f92,f63])).

fof(f1242,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK2,k7_lattices(sK0,sK1)),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1241,f336])).

fof(f1241,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2))) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_20
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f1053,f525])).

fof(f1053,plain,
    ( k7_lattices(sK0,k4_lattices(sK0,k4_filter_0(sK0,sK2,sK1),k4_filter_0(sK0,sK1,sK2))) = k3_lattices(sK0,k7_lattices(sK0,k4_filter_0(sK0,sK2,sK1)),k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_24
    | ~ spl3_25 ),
    inference(unit_resulting_resolution,[],[f77,f82,f72,f87,f618,f623,f60])).

fof(f629,plain,
    ( spl3_26
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f133,f95,f85,f75,f70,f626])).

fof(f626,plain,
    ( spl3_26
  <=> m1_subset_1(k4_filter_0(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f133,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK1,sK1),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f72,f87,f77,f97,f97,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_filter_0)).

fof(f624,plain,
    ( spl3_25
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f132,f95,f90,f85,f75,f70,f621])).

fof(f132,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f72,f87,f77,f92,f97,f68])).

fof(f619,plain,
    ( spl3_24
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f131,f95,f90,f85,f75,f70,f616])).

fof(f131,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK2,sK1),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f72,f87,f77,f97,f92,f68])).

fof(f614,plain,
    ( spl3_23
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f130,f90,f85,f75,f70,f611])).

fof(f611,plain,
    ( spl3_23
  <=> m1_subset_1(k4_filter_0(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f130,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK2,sK2),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f72,f87,f77,f92,f92,f68])).

fof(f609,plain,
    ( spl3_22
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f120,f95,f85,f80,f75,f70,f606])).

fof(f606,plain,
    ( spl3_22
  <=> sK1 = k7_lattices(sK0,k7_lattices(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f604,plain,
    ( spl3_21
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f119,f90,f85,f80,f75,f70,f601])).

fof(f601,plain,
    ( spl3_21
  <=> sK2 = k7_lattices(sK0,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f599,plain,
    ( ~ spl3_12
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_11
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f595,f244,f239,f184,f126,f113,f95,f90,f85,f80,f75,f70,f188])).

fof(f184,plain,
    ( spl3_11
  <=> k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) = k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f595,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_11
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f533,f594])).

fof(f533,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_9
    | spl3_11
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f186,f531])).

fof(f531,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k7_filter_0(sK0,sK2,k7_lattices(sK0,sK1))
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
    inference(backward_demodulation,[],[f490,f527])).

fof(f490,plain,
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
    inference(forward_demodulation,[],[f489,f335])).

fof(f489,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK2),k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f405,f120])).

fof(f405,plain,
    ( k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) = k3_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK1),sK2),k4_lattices(sK0,k7_lattices(sK0,k7_lattices(sK0,sK1)),k7_lattices(sK0,sK2)))
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_20 ),
    inference(unit_resulting_resolution,[],[f77,f72,f82,f87,f92,f246,f62])).

fof(f186,plain,
    ( k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2)
    | spl3_11 ),
    inference(avatar_component_clause,[],[f184])).

fof(f247,plain,
    ( spl3_20
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f118,f95,f85,f70,f244])).

fof(f118,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f72,f87,f97,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f242,plain,
    ( spl3_19
    | spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f117,f90,f85,f70,f239])).

fof(f117,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f72,f87,f92,f64])).

fof(f219,plain,
    ( spl3_18
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f111,f85,f75,f70,f216])).

fof(f216,plain,
    ( spl3_18
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f111,plain,
    ( v9_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f87,f77,f72,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f214,plain,
    ( spl3_17
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f110,f85,f75,f70,f211])).

fof(f211,plain,
    ( spl3_17
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f110,plain,
    ( v8_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f87,f77,f72,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f209,plain,
    ( spl3_16
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f109,f85,f75,f70,f206])).

fof(f206,plain,
    ( spl3_16
  <=> v7_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f109,plain,
    ( v7_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f87,f77,f72,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f204,plain,
    ( spl3_15
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f108,f85,f75,f70,f201])).

fof(f201,plain,
    ( spl3_15
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f108,plain,
    ( v6_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f87,f77,f72,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f199,plain,
    ( ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f43,f196,f192,f188,f184])).

fof(f43,plain,
    ( k7_lattices(sK0,k4_filter_0(sK0,sK1,sK2)) != k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k3_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),sK2))
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,sK1,k7_lattices(sK0,sK2))
    | k7_lattices(sK0,k7_filter_0(sK0,sK1,sK2)) != k7_filter_0(sK0,k7_lattices(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_filter_1)).

fof(f154,plain,
    ( spl3_10
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f102,f85,f75,f70,f151])).

fof(f151,plain,
    ( spl3_10
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f102,plain,
    ( v5_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f87,f77,f72,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f129,plain,
    ( spl3_9
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f101,f85,f75,f70,f126])).

fof(f101,plain,
    ( v4_lattices(sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f87,f77,f72,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f116,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f100,f85,f113])).

fof(f100,plain,
    ( l2_lattices(sK0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f87,f51])).

fof(f51,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f107,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f99,f85,f104])).

fof(f104,plain,
    ( spl3_7
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f99,plain,
    ( l1_lattices(sK0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f87,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f45,f95])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f93,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f44,f90])).

fof(f44,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f49,f85])).

fof(f49,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f83,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f48,f80])).

fof(f48,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f78,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f47,f75])).

fof(f47,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f73,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f46,f70])).

fof(f46,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
