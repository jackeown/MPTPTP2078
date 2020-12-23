%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 571 expanded)
%              Number of leaves         :   42 ( 246 expanded)
%              Depth                    :   14
%              Number of atoms          : 1071 (2239 expanded)
%              Number of equality atoms :  123 ( 305 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1920,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f95,f100,f105,f110,f115,f132,f135,f140,f151,f180,f185,f190,f198,f211,f216,f249,f274,f380,f408,f525,f573,f657,f704,f1086,f1315,f1865,f1887,f1919])).

fof(f1919,plain,
    ( spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_64
    | ~ spl4_94 ),
    inference(avatar_contradiction_clause,[],[f1918])).

fof(f1918,plain,
    ( $false
    | spl4_5
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_64
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f1917,f80])).

fof(f80,plain,
    ( sK2 != sK3
    | spl4_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_5
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1917,plain,
    ( sK2 = sK3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_64
    | ~ spl4_94 ),
    inference(forward_demodulation,[],[f1916,f1314])).

fof(f1314,plain,
    ( sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3))
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f1312])).

fof(f1312,plain,
    ( spl4_64
  <=> sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f1916,plain,
    ( sK3 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_16
    | ~ spl4_94 ),
    inference(forward_demodulation,[],[f1915,f114])).

fof(f114,plain,
    ( k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl4_10
  <=> k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1915,plain,
    ( sK3 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK2,sK3))
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f1914,f104])).

fof(f104,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1914,plain,
    ( sK3 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_94 ),
    inference(subsumption_resolution,[],[f1905,f94])).

fof(f94,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1905,plain,
    ( sK3 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_16
    | ~ spl4_94 ),
    inference(superposition,[],[f1886,f175])).

fof(f175,plain,
    ( ! [X2,X3] :
        ( k3_lattices(sK0,X2,X3) = k3_lattices(sK0,X3,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl4_16
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,X2,X3) = k3_lattices(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f1886,plain,
    ( sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3))
    | ~ spl4_94 ),
    inference(avatar_component_clause,[],[f1884])).

fof(f1884,plain,
    ( spl4_94
  <=> sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f1887,plain,
    ( spl4_94
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_93 ),
    inference(avatar_split_clause,[],[f1879,f1862,f174,f97,f92,f1884])).

fof(f97,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

% (27669)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f1862,plain,
    ( spl4_93
  <=> sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f1879,plain,
    ( sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3))
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_93 ),
    inference(subsumption_resolution,[],[f1878,f94])).

fof(f1878,plain,
    ( sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_93 ),
    inference(subsumption_resolution,[],[f1868,f99])).

fof(f99,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f97])).

fof(f1868,plain,
    ( sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl4_16
    | ~ spl4_93 ),
    inference(superposition,[],[f1864,f175])).

fof(f1864,plain,
    ( sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,sK2))
    | ~ spl4_93 ),
    inference(avatar_component_clause,[],[f1862])).

fof(f1865,plain,
    ( spl4_93
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f1858,f701,f102,f97,f92,f73,f68,f63,f58,f1862])).

fof(f58,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f63,plain,
    ( spl4_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f68,plain,
    ( spl4_3
  <=> v11_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f73,plain,
    ( spl4_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f701,plain,
    ( spl4_38
  <=> sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f1858,plain,
    ( sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,sK2))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f647,f703])).

fof(f703,plain,
    ( sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f701])).

fof(f647,plain,
    ( k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,sK2))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(resolution,[],[f347,f99])).

fof(f347,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,X4)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,X4)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(resolution,[],[f238,f104])).

fof(f238,plain,
    ( ! [X10,X11] :
        ( ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | k3_lattices(sK0,sK3,k4_lattices(sK0,X10,X11)) = k4_lattices(sK0,k3_lattices(sK0,sK3,X10),k3_lattices(sK0,sK3,X11)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(resolution,[],[f228,f94])).

fof(f228,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,X0,k4_lattices(sK0,X1,X2)) = k4_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f90,f75])).

fof(f75,plain,
    ( l3_lattices(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f90,plain,
    ( ! [X2,X0,X1] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,X0,k4_lattices(sK0,X1,X2)) = k4_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f89,f60])).

fof(f60,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f89,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,X0,k4_lattices(sK0,X1,X2)) = k4_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2)) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f88,f65])).

fof(f65,plain,
    ( v10_lattices(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f88,plain,
    ( ! [X2,X0,X1] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k3_lattices(sK0,X0,k4_lattices(sK0,X1,X2)) = k4_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f70,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v11_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).

fof(f70,plain,
    ( v11_lattices(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f1315,plain,
    ( spl4_64
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f1099,f1083,f174,f102,f97,f1312])).

fof(f1083,plain,
    ( spl4_53
  <=> sK2 = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f1099,plain,
    ( sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3))
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f1098,f99])).

fof(f1098,plain,
    ( sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_8
    | ~ spl4_16
    | ~ spl4_53 ),
    inference(subsumption_resolution,[],[f1094,f104])).

fof(f1094,plain,
    ( sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_16
    | ~ spl4_53 ),
    inference(superposition,[],[f1085,f175])).

fof(f1085,plain,
    ( sK2 = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3))
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f1083])).

fof(f1086,plain,
    ( spl4_53
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f631,f570,f107,f102,f97,f92,f73,f68,f63,f58,f1083])).

fof(f107,plain,
    ( spl4_9
  <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f570,plain,
    ( spl4_36
  <=> sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f631,plain,
    ( sK2 = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f630,f572])).

fof(f572,plain,
    ( sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f570])).

fof(f630,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f624,f109])).

fof(f109,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f624,plain,
    ( k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(resolution,[],[f335,f94])).

fof(f335,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,X4)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,X4)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(resolution,[],[f237,f104])).

fof(f237,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k3_lattices(sK0,sK2,k4_lattices(sK0,X8,X9)) = k4_lattices(sK0,k3_lattices(sK0,sK2,X8),k3_lattices(sK0,sK2,X9)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(resolution,[],[f228,f99])).

fof(f704,plain,
    ( spl4_38
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_16
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f672,f654,f174,f129,f92,f701])).

fof(f129,plain,
    ( spl4_13
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f654,plain,
    ( spl4_37
  <=> sK3 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f672,plain,
    ( sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2))
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_16
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f671,f131])).

fof(f131,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f671,plain,
    ( sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl4_6
    | ~ spl4_16
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f667,f94])).

fof(f667,plain,
    ( sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl4_16
    | ~ spl4_37 ),
    inference(superposition,[],[f656,f175])).

fof(f656,plain,
    ( sK3 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f654])).

fof(f657,plain,
    ( spl4_37
    | spl4_1
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f419,f405,f177,f145,f129,f92,f58,f654])).

fof(f145,plain,
    ( spl4_15
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f177,plain,
    ( spl4_17
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f405,plain,
    ( spl4_30
  <=> sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f419,plain,
    ( sK3 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | spl4_1
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f418,f131])).

fof(f418,plain,
    ( sK3 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_6
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f414,f94])).

fof(f414,plain,
    ( sK3 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_30 ),
    inference(superposition,[],[f407,f193])).

fof(f193,plain,
    ( ! [X4,X5] :
        ( k3_lattices(sK0,X4,X5) = k1_lattices(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_15
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f192,f146])).

fof(f146,plain,
    ( l2_lattices(sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f192,plain,
    ( ! [X4,X5] :
        ( ~ l2_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k3_lattices(sK0,X4,X5) = k1_lattices(sK0,X4,X5) )
    | spl4_1
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f84,f178])).

fof(f178,plain,
    ( v4_lattices(sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f177])).

fof(f84,plain,
    ( ! [X4,X5] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k3_lattices(sK0,X4,X5) = k1_lattices(sK0,X4,X5) )
    | spl4_1 ),
    inference(resolution,[],[f60,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f407,plain,
    ( sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f405])).

fof(f573,plain,
    ( spl4_36
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_16
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f542,f522,f174,f129,f97,f570])).

fof(f522,plain,
    ( spl4_35
  <=> sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f542,plain,
    ( sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_16
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f541,f131])).

fof(f541,plain,
    ( sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f537,f99])).

fof(f537,plain,
    ( sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl4_16
    | ~ spl4_35 ),
    inference(superposition,[],[f524,f175])).

fof(f524,plain,
    ( sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f522])).

fof(f525,plain,
    ( spl4_35
    | spl4_1
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f390,f377,f177,f145,f129,f97,f58,f522])).

fof(f377,plain,
    ( spl4_28
  <=> sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f390,plain,
    ( sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | spl4_1
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f389,f131])).

fof(f389,plain,
    ( sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_7
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f385,f99])).

fof(f385,plain,
    ( sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_28 ),
    inference(superposition,[],[f379,f193])).

fof(f379,plain,
    ( sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f377])).

fof(f408,plain,
    ( spl4_30
    | spl4_1
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f279,f271,f145,f129,f92,f58,f405])).

fof(f271,plain,
    ( spl4_24
  <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f279,plain,
    ( sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | spl4_1
    | ~ spl4_6
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f278,f131])).

fof(f278,plain,
    ( sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_6
    | ~ spl4_15
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f277,f94])).

fof(f277,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_15
    | ~ spl4_24 ),
    inference(resolution,[],[f273,f152])).

fof(f152,plain,
    ( ! [X8,X9] :
        ( ~ r1_lattices(sK0,X8,X9)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k1_lattices(sK0,X8,X9) = X9
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | spl4_1
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f86,f146])).

fof(f86,plain,
    ( ! [X8,X9] :
        ( ~ l2_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | k1_lattices(sK0,X8,X9) = X9
        | ~ r1_lattices(sK0,X8,X9) )
    | spl4_1 ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(f273,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f271])).

fof(f380,plain,
    ( spl4_28
    | spl4_1
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f260,f246,f145,f129,f97,f58,f377])).

fof(f246,plain,
    ( spl4_23
  <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f260,plain,
    ( sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | spl4_1
    | ~ spl4_7
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f259,f131])).

fof(f259,plain,
    ( sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_7
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f258,f99])).

fof(f258,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl4_1
    | ~ spl4_15
    | ~ spl4_23 ),
    inference(resolution,[],[f248,f152])).

fof(f248,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f246])).

fof(f274,plain,
    ( spl4_24
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f227,f205,f195,f102,f92,f271])).

fof(f195,plain,
    ( spl4_19
  <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f205,plain,
    ( spl4_20
  <=> ! [X11,X10] :
        ( ~ m1_subset_1(X10,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X10,X11),X10)
        | ~ m1_subset_1(X11,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f227,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f226,f104])).

fof(f226,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_6
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f220,f94])).

fof(f220,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(superposition,[],[f206,f197])).

fof(f197,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f195])).

fof(f206,plain,
    ( ! [X10,X11] :
        ( r1_lattices(sK0,k4_lattices(sK0,X10,X11),X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0)) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f205])).

fof(f249,plain,
    ( spl4_23
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f225,f205,f187,f102,f97,f246])).

fof(f187,plain,
    ( spl4_18
  <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f225,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f224,f104])).

fof(f224,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_7
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f219,f99])).

fof(f219,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(superposition,[],[f206,f189])).

fof(f189,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f187])).

fof(f216,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_21 ),
    inference(subsumption_resolution,[],[f214,f75])).

fof(f214,plain,
    ( ~ l3_lattices(sK0)
    | spl4_1
    | ~ spl4_2
    | spl4_21 ),
    inference(subsumption_resolution,[],[f213,f65])).

fof(f213,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl4_1
    | spl4_21 ),
    inference(subsumption_resolution,[],[f212,f60])).

fof(f212,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl4_21 ),
    inference(resolution,[],[f210,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f210,plain,
    ( ~ v8_lattices(sK0)
    | spl4_21 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_21
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f211,plain,
    ( spl4_20
    | ~ spl4_21
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f202,f125,f73,f58,f208,f205])).

fof(f125,plain,
    ( spl4_12
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f202,plain,
    ( ! [X10,X11] :
        ( ~ v8_lattices(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X10,X11),X10) )
    | spl4_1
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f201,f75])).

fof(f201,plain,
    ( ! [X10,X11] :
        ( ~ v8_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X10,X11),X10) )
    | spl4_1
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f87,f126])).

fof(f126,plain,
    ( v6_lattices(sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f87,plain,
    ( ! [X10,X11] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X10,X11),X10) )
    | spl4_1 ),
    inference(resolution,[],[f60,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).

fof(f198,plain,
    ( spl4_19
    | spl4_1
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f171,f125,f121,f107,f102,f92,f58,f195])).

fof(f121,plain,
    ( spl4_11
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f171,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1)
    | spl4_1
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f167,f109])).

fof(f167,plain,
    ( k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1)
    | spl4_1
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f157,f94])).

fof(f157,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k4_lattices(sK0,sK1,X4) = k4_lattices(sK0,X4,sK1) )
    | spl4_1
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f154,f104])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) )
    | spl4_1
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f153,f122])).

fof(f122,plain,
    ( l1_lattices(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) )
    | spl4_1
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f82,f126])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ v6_lattices(sK0)
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) )
    | spl4_1 ),
    inference(resolution,[],[f60,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f190,plain,
    ( spl4_18
    | spl4_1
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f166,f125,f121,f102,f97,f58,f187])).

fof(f166,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)
    | spl4_1
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(resolution,[],[f157,f99])).

fof(f185,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_17 ),
    inference(subsumption_resolution,[],[f183,f75])).

fof(f183,plain,
    ( ~ l3_lattices(sK0)
    | spl4_1
    | ~ spl4_2
    | spl4_17 ),
    inference(subsumption_resolution,[],[f182,f65])).

fof(f182,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl4_1
    | spl4_17 ),
    inference(subsumption_resolution,[],[f181,f60])).

fof(f181,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl4_17 ),
    inference(resolution,[],[f179,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f179,plain,
    ( ~ v4_lattices(sK0)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f177])).

fof(f180,plain,
    ( spl4_16
    | ~ spl4_17
    | spl4_1
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f172,f145,f58,f177,f174])).

fof(f172,plain,
    ( ! [X2,X3] :
        ( ~ v4_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,X2,X3) = k3_lattices(sK0,X3,X2) )
    | spl4_1
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f83,f146])).

fof(f83,plain,
    ( ! [X2,X3] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,X2,X3) = k3_lattices(sK0,X3,X2) )
    | spl4_1 ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f151,plain,
    ( ~ spl4_4
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | ~ spl4_4
    | spl4_15 ),
    inference(subsumption_resolution,[],[f149,f75])).

fof(f149,plain,
    ( ~ l3_lattices(sK0)
    | spl4_15 ),
    inference(resolution,[],[f147,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f147,plain,
    ( ~ l2_lattices(sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f145])).

fof(f140,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_12 ),
    inference(subsumption_resolution,[],[f138,f75])).

fof(f138,plain,
    ( ~ l3_lattices(sK0)
    | spl4_1
    | ~ spl4_2
    | spl4_12 ),
    inference(subsumption_resolution,[],[f137,f65])).

fof(f137,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl4_1
    | spl4_12 ),
    inference(subsumption_resolution,[],[f136,f60])).

fof(f136,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl4_12 ),
    inference(resolution,[],[f127,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f127,plain,
    ( ~ v6_lattices(sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f135,plain,
    ( ~ spl4_4
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl4_4
    | spl4_11 ),
    inference(subsumption_resolution,[],[f133,f75])).

fof(f133,plain,
    ( ~ l3_lattices(sK0)
    | spl4_11 ),
    inference(resolution,[],[f123,f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f123,plain,
    ( ~ l1_lattices(sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f132,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | spl4_13
    | spl4_1
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f119,f107,f102,f92,f58,f129,f125,f121])).

fof(f119,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | spl4_1
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f118,f60])).

fof(f118,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f117,f94])).

fof(f117,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f116,f104])).

fof(f116,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(superposition,[],[f55,f109])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f115,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f33,f112])).

fof(f33,plain,(
    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( X2 != X3
                  & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                  & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v11_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v11_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                        & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                     => X2 = X3 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v11_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3)
                      & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) )
                   => X2 = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_lattices)).

fof(f110,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f32,f107])).

fof(f32,plain,(
    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f105,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f36,f102])).

fof(f36,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f100,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f35,f97])).

fof(f35,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f95,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f31,f92])).

fof(f31,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f13])).

fof(f76,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f40,f73])).

fof(f40,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f39,f68])).

fof(f39,plain,(
    v11_lattices(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f38,f63])).

fof(f38,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f37,f58])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:21:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (27663)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (27663)Refutation not found, incomplete strategy% (27663)------------------------------
% 0.21/0.47  % (27663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (27663)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (27663)Memory used [KB]: 6396
% 0.21/0.47  % (27663)Time elapsed: 0.038 s
% 0.21/0.47  % (27663)------------------------------
% 0.21/0.47  % (27663)------------------------------
% 0.21/0.49  % (27653)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (27661)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (27656)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (27658)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (27662)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.53  % (27654)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (27672)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.53  % (27668)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (27659)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.53  % (27657)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.53  % (27655)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.54  % (27664)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.54  % (27667)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.54  % (27660)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.55  % (27673)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.55  % (27673)Refutation not found, incomplete strategy% (27673)------------------------------
% 0.21/0.55  % (27673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27673)Memory used [KB]: 10618
% 0.21/0.55  % (27673)Time elapsed: 0.122 s
% 0.21/0.55  % (27673)------------------------------
% 0.21/0.55  % (27673)------------------------------
% 0.21/0.56  % (27656)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f1920,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f61,f66,f71,f76,f81,f95,f100,f105,f110,f115,f132,f135,f140,f151,f180,f185,f190,f198,f211,f216,f249,f274,f380,f408,f525,f573,f657,f704,f1086,f1315,f1865,f1887,f1919])).
% 0.21/0.56  fof(f1919,plain,(
% 0.21/0.56    spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_16 | ~spl4_64 | ~spl4_94),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f1918])).
% 0.21/0.56  fof(f1918,plain,(
% 0.21/0.56    $false | (spl4_5 | ~spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_16 | ~spl4_64 | ~spl4_94)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1917,f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    sK2 != sK3 | spl4_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f78])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    spl4_5 <=> sK2 = sK3),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.56  fof(f1917,plain,(
% 0.21/0.56    sK2 = sK3 | (~spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_16 | ~spl4_64 | ~spl4_94)),
% 0.21/0.56    inference(forward_demodulation,[],[f1916,f1314])).
% 0.21/0.56  fof(f1314,plain,(
% 0.21/0.56    sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) | ~spl4_64),
% 0.21/0.56    inference(avatar_component_clause,[],[f1312])).
% 0.21/0.56  fof(f1312,plain,(
% 0.21/0.56    spl4_64 <=> sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.21/0.56  fof(f1916,plain,(
% 0.21/0.56    sK3 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) | (~spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_16 | ~spl4_94)),
% 0.21/0.56    inference(forward_demodulation,[],[f1915,f114])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3) | ~spl4_10),
% 0.21/0.56    inference(avatar_component_clause,[],[f112])).
% 0.21/0.56  fof(f112,plain,(
% 0.21/0.56    spl4_10 <=> k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.56  fof(f1915,plain,(
% 0.21/0.56    sK3 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK2,sK3)) | (~spl4_6 | ~spl4_8 | ~spl4_16 | ~spl4_94)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1914,f104])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f102])).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    spl4_8 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.56  fof(f1914,plain,(
% 0.21/0.56    sK3 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK2,sK3)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl4_6 | ~spl4_16 | ~spl4_94)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1905,f94])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl4_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f92])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    spl4_6 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.56  fof(f1905,plain,(
% 0.21/0.56    sK3 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK3),k3_lattices(sK0,sK2,sK3)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl4_16 | ~spl4_94)),
% 0.21/0.56    inference(superposition,[],[f1886,f175])).
% 0.21/0.56  fof(f175,plain,(
% 0.21/0.56    ( ! [X2,X3] : (k3_lattices(sK0,X2,X3) = k3_lattices(sK0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl4_16),
% 0.21/0.56    inference(avatar_component_clause,[],[f174])).
% 0.21/0.56  fof(f174,plain,(
% 0.21/0.56    spl4_16 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k3_lattices(sK0,X2,X3) = k3_lattices(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.56  fof(f1886,plain,(
% 0.21/0.56    sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3)) | ~spl4_94),
% 0.21/0.56    inference(avatar_component_clause,[],[f1884])).
% 0.21/0.56  fof(f1884,plain,(
% 0.21/0.56    spl4_94 <=> sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).
% 0.21/0.56  fof(f1887,plain,(
% 0.21/0.56    spl4_94 | ~spl4_6 | ~spl4_7 | ~spl4_16 | ~spl4_93),
% 0.21/0.56    inference(avatar_split_clause,[],[f1879,f1862,f174,f97,f92,f1884])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    spl4_7 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.56  % (27669)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.56  fof(f1862,plain,(
% 0.21/0.56    spl4_93 <=> sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 0.21/0.56  fof(f1879,plain,(
% 0.21/0.56    sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3)) | (~spl4_6 | ~spl4_7 | ~spl4_16 | ~spl4_93)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1878,f94])).
% 0.21/0.56  fof(f1878,plain,(
% 0.21/0.56    sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl4_7 | ~spl4_16 | ~spl4_93)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1868,f99])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f97])).
% 0.21/0.56  fof(f1868,plain,(
% 0.21/0.56    sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK2,sK3)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl4_16 | ~spl4_93)),
% 0.21/0.56    inference(superposition,[],[f1864,f175])).
% 0.21/0.56  fof(f1864,plain,(
% 0.21/0.56    sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,sK2)) | ~spl4_93),
% 0.21/0.56    inference(avatar_component_clause,[],[f1862])).
% 0.21/0.56  fof(f1865,plain,(
% 0.21/0.56    spl4_93 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_38),
% 0.21/0.56    inference(avatar_split_clause,[],[f1858,f701,f102,f97,f92,f73,f68,f63,f58,f1862])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    spl4_2 <=> v10_lattices(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    spl4_3 <=> v11_lattices(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    spl4_4 <=> l3_lattices(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.56  fof(f701,plain,(
% 0.21/0.56    spl4_38 <=> sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.56  fof(f1858,plain,(
% 0.21/0.56    sK3 = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,sK2)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_38)),
% 0.21/0.56    inference(forward_demodulation,[],[f647,f703])).
% 0.21/0.56  fof(f703,plain,(
% 0.21/0.56    sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) | ~spl4_38),
% 0.21/0.56    inference(avatar_component_clause,[],[f701])).
% 0.21/0.56  fof(f647,plain,(
% 0.21/0.56    k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,sK2)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 0.21/0.56    inference(resolution,[],[f347,f99])).
% 0.21/0.56  fof(f347,plain,(
% 0.21/0.56    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,X4)) = k4_lattices(sK0,k3_lattices(sK0,sK3,sK1),k3_lattices(sK0,sK3,X4))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_8)),
% 0.21/0.56    inference(resolution,[],[f238,f104])).
% 0.21/0.56  fof(f238,plain,(
% 0.21/0.56    ( ! [X10,X11] : (~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | k3_lattices(sK0,sK3,k4_lattices(sK0,X10,X11)) = k4_lattices(sK0,k3_lattices(sK0,sK3,X10),k3_lattices(sK0,sK3,X11))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6)),
% 0.21/0.56    inference(resolution,[],[f228,f94])).
% 0.21/0.56  fof(f228,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k3_lattices(sK0,X0,k4_lattices(sK0,X1,X2)) = k4_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f90,f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    l3_lattices(sK0) | ~spl4_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f73])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k3_lattices(sK0,X0,k4_lattices(sK0,X1,X2)) = k4_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2))) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f89,f60])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f58])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k3_lattices(sK0,X0,k4_lattices(sK0,X1,X2)) = k4_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2))) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f88,f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    v10_lattices(sK0) | ~spl4_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f63])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | k3_lattices(sK0,X0,k4_lattices(sK0,X1,X2)) = k4_lattices(sK0,k3_lattices(sK0,X0,X1),k3_lattices(sK0,X0,X2))) ) | ~spl4_3),
% 0.21/0.56    inference(resolution,[],[f70,f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v11_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => k3_lattices(X0,X1,k4_lattices(X0,X2,X3)) = k4_lattices(X0,k3_lattices(X0,X1,X2),k3_lattices(X0,X1,X3))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_lattices)).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    v11_lattices(sK0) | ~spl4_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f68])).
% 0.21/0.56  fof(f1315,plain,(
% 0.21/0.56    spl4_64 | ~spl4_7 | ~spl4_8 | ~spl4_16 | ~spl4_53),
% 0.21/0.56    inference(avatar_split_clause,[],[f1099,f1083,f174,f102,f97,f1312])).
% 0.21/0.56  fof(f1083,plain,(
% 0.21/0.56    spl4_53 <=> sK2 = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 0.21/0.56  fof(f1099,plain,(
% 0.21/0.56    sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) | (~spl4_7 | ~spl4_8 | ~spl4_16 | ~spl4_53)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1098,f99])).
% 0.21/0.56  fof(f1098,plain,(
% 0.21/0.56    sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl4_8 | ~spl4_16 | ~spl4_53)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1094,f104])).
% 0.21/0.56  fof(f1094,plain,(
% 0.21/0.56    sK2 = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k3_lattices(sK0,sK2,sK3)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl4_16 | ~spl4_53)),
% 0.21/0.56    inference(superposition,[],[f1085,f175])).
% 0.21/0.56  fof(f1085,plain,(
% 0.21/0.56    sK2 = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3)) | ~spl4_53),
% 0.21/0.56    inference(avatar_component_clause,[],[f1083])).
% 0.21/0.56  fof(f1086,plain,(
% 0.21/0.56    spl4_53 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36),
% 0.21/0.56    inference(avatar_split_clause,[],[f631,f570,f107,f102,f97,f92,f73,f68,f63,f58,f1083])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    spl4_9 <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.56  fof(f570,plain,(
% 0.21/0.56    spl4_36 <=> sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.56  fof(f631,plain,(
% 0.21/0.56    sK2 = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_36)),
% 0.21/0.56    inference(forward_demodulation,[],[f630,f572])).
% 0.21/0.56  fof(f572,plain,(
% 0.21/0.56    sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) | ~spl4_36),
% 0.21/0.56    inference(avatar_component_clause,[],[f570])).
% 0.21/0.56  fof(f630,plain,(
% 0.21/0.56    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9)),
% 0.21/0.56    inference(forward_demodulation,[],[f624,f109])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3) | ~spl4_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f107])).
% 0.21/0.56  fof(f624,plain,(
% 0.21/0.56    k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK3)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,sK3)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 0.21/0.56    inference(resolution,[],[f335,f94])).
% 0.21/0.56  fof(f335,plain,(
% 0.21/0.56    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,X4)) = k4_lattices(sK0,k3_lattices(sK0,sK2,sK1),k3_lattices(sK0,sK2,X4))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_8)),
% 0.21/0.56    inference(resolution,[],[f237,f104])).
% 0.21/0.56  fof(f237,plain,(
% 0.21/0.56    ( ! [X8,X9] : (~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | k3_lattices(sK0,sK2,k4_lattices(sK0,X8,X9)) = k4_lattices(sK0,k3_lattices(sK0,sK2,X8),k3_lattices(sK0,sK2,X9))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.56    inference(resolution,[],[f228,f99])).
% 0.21/0.56  fof(f704,plain,(
% 0.21/0.56    spl4_38 | ~spl4_6 | ~spl4_13 | ~spl4_16 | ~spl4_37),
% 0.21/0.56    inference(avatar_split_clause,[],[f672,f654,f174,f129,f92,f701])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    spl4_13 <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.56  fof(f654,plain,(
% 0.21/0.56    spl4_37 <=> sK3 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.56  fof(f672,plain,(
% 0.21/0.56    sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) | (~spl4_6 | ~spl4_13 | ~spl4_16 | ~spl4_37)),
% 0.21/0.56    inference(subsumption_resolution,[],[f671,f131])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~spl4_13),
% 0.21/0.56    inference(avatar_component_clause,[],[f129])).
% 0.21/0.56  fof(f671,plain,(
% 0.21/0.56    sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl4_6 | ~spl4_16 | ~spl4_37)),
% 0.21/0.56    inference(subsumption_resolution,[],[f667,f94])).
% 0.21/0.56  fof(f667,plain,(
% 0.21/0.56    sK3 = k3_lattices(sK0,sK3,k4_lattices(sK0,sK1,sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl4_16 | ~spl4_37)),
% 0.21/0.56    inference(superposition,[],[f656,f175])).
% 0.21/0.56  fof(f656,plain,(
% 0.21/0.56    sK3 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | ~spl4_37),
% 0.21/0.56    inference(avatar_component_clause,[],[f654])).
% 0.21/0.56  fof(f657,plain,(
% 0.21/0.56    spl4_37 | spl4_1 | ~spl4_6 | ~spl4_13 | ~spl4_15 | ~spl4_17 | ~spl4_30),
% 0.21/0.56    inference(avatar_split_clause,[],[f419,f405,f177,f145,f129,f92,f58,f654])).
% 0.21/0.56  fof(f145,plain,(
% 0.21/0.56    spl4_15 <=> l2_lattices(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.56  fof(f177,plain,(
% 0.21/0.56    spl4_17 <=> v4_lattices(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.56  fof(f405,plain,(
% 0.21/0.56    spl4_30 <=> sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.56  fof(f419,plain,(
% 0.21/0.56    sK3 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | (spl4_1 | ~spl4_6 | ~spl4_13 | ~spl4_15 | ~spl4_17 | ~spl4_30)),
% 0.21/0.56    inference(subsumption_resolution,[],[f418,f131])).
% 0.21/0.56  fof(f418,plain,(
% 0.21/0.56    sK3 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl4_1 | ~spl4_6 | ~spl4_15 | ~spl4_17 | ~spl4_30)),
% 0.21/0.56    inference(subsumption_resolution,[],[f414,f94])).
% 0.21/0.56  fof(f414,plain,(
% 0.21/0.56    sK3 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl4_1 | ~spl4_15 | ~spl4_17 | ~spl4_30)),
% 0.21/0.56    inference(superposition,[],[f407,f193])).
% 0.21/0.56  fof(f193,plain,(
% 0.21/0.56    ( ! [X4,X5] : (k3_lattices(sK0,X4,X5) = k1_lattices(sK0,X4,X5) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | (spl4_1 | ~spl4_15 | ~spl4_17)),
% 0.21/0.56    inference(subsumption_resolution,[],[f192,f146])).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    l2_lattices(sK0) | ~spl4_15),
% 0.21/0.56    inference(avatar_component_clause,[],[f145])).
% 0.21/0.56  fof(f192,plain,(
% 0.21/0.56    ( ! [X4,X5] : (~l2_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k3_lattices(sK0,X4,X5) = k1_lattices(sK0,X4,X5)) ) | (spl4_1 | ~spl4_17)),
% 0.21/0.56    inference(subsumption_resolution,[],[f84,f178])).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    v4_lattices(sK0) | ~spl4_17),
% 0.21/0.56    inference(avatar_component_clause,[],[f177])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X4,X5] : (~v4_lattices(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k3_lattices(sK0,X4,X5) = k1_lattices(sK0,X4,X5)) ) | spl4_1),
% 0.21/0.56    inference(resolution,[],[f60,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v4_lattices(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.21/0.56  fof(f407,plain,(
% 0.21/0.56    sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | ~spl4_30),
% 0.21/0.56    inference(avatar_component_clause,[],[f405])).
% 0.21/0.56  fof(f573,plain,(
% 0.21/0.56    spl4_36 | ~spl4_7 | ~spl4_13 | ~spl4_16 | ~spl4_35),
% 0.21/0.56    inference(avatar_split_clause,[],[f542,f522,f174,f129,f97,f570])).
% 0.21/0.56  fof(f522,plain,(
% 0.21/0.56    spl4_35 <=> sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.56  fof(f542,plain,(
% 0.21/0.56    sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) | (~spl4_7 | ~spl4_13 | ~spl4_16 | ~spl4_35)),
% 0.21/0.56    inference(subsumption_resolution,[],[f541,f131])).
% 0.21/0.56  fof(f541,plain,(
% 0.21/0.56    sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl4_7 | ~spl4_16 | ~spl4_35)),
% 0.21/0.56    inference(subsumption_resolution,[],[f537,f99])).
% 0.21/0.56  fof(f537,plain,(
% 0.21/0.56    sK2 = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl4_16 | ~spl4_35)),
% 0.21/0.56    inference(superposition,[],[f524,f175])).
% 0.21/0.56  fof(f524,plain,(
% 0.21/0.56    sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | ~spl4_35),
% 0.21/0.56    inference(avatar_component_clause,[],[f522])).
% 0.21/0.56  fof(f525,plain,(
% 0.21/0.56    spl4_35 | spl4_1 | ~spl4_7 | ~spl4_13 | ~spl4_15 | ~spl4_17 | ~spl4_28),
% 0.21/0.56    inference(avatar_split_clause,[],[f390,f377,f177,f145,f129,f97,f58,f522])).
% 0.21/0.56  fof(f377,plain,(
% 0.21/0.56    spl4_28 <=> sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.56  fof(f390,plain,(
% 0.21/0.56    sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | (spl4_1 | ~spl4_7 | ~spl4_13 | ~spl4_15 | ~spl4_17 | ~spl4_28)),
% 0.21/0.56    inference(subsumption_resolution,[],[f389,f131])).
% 0.21/0.56  fof(f389,plain,(
% 0.21/0.56    sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl4_1 | ~spl4_7 | ~spl4_15 | ~spl4_17 | ~spl4_28)),
% 0.21/0.56    inference(subsumption_resolution,[],[f385,f99])).
% 0.21/0.56  fof(f385,plain,(
% 0.21/0.56    sK2 = k3_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl4_1 | ~spl4_15 | ~spl4_17 | ~spl4_28)),
% 0.21/0.56    inference(superposition,[],[f379,f193])).
% 0.21/0.56  fof(f379,plain,(
% 0.21/0.56    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | ~spl4_28),
% 0.21/0.56    inference(avatar_component_clause,[],[f377])).
% 0.21/0.56  fof(f408,plain,(
% 0.21/0.56    spl4_30 | spl4_1 | ~spl4_6 | ~spl4_13 | ~spl4_15 | ~spl4_24),
% 0.21/0.56    inference(avatar_split_clause,[],[f279,f271,f145,f129,f92,f58,f405])).
% 0.21/0.56  fof(f271,plain,(
% 0.21/0.56    spl4_24 <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.56  fof(f279,plain,(
% 0.21/0.56    sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | (spl4_1 | ~spl4_6 | ~spl4_13 | ~spl4_15 | ~spl4_24)),
% 0.21/0.56    inference(subsumption_resolution,[],[f278,f131])).
% 0.21/0.56  fof(f278,plain,(
% 0.21/0.56    sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl4_1 | ~spl4_6 | ~spl4_15 | ~spl4_24)),
% 0.21/0.56    inference(subsumption_resolution,[],[f277,f94])).
% 0.21/0.56  fof(f277,plain,(
% 0.21/0.56    ~m1_subset_1(sK3,u1_struct_0(sK0)) | sK3 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl4_1 | ~spl4_15 | ~spl4_24)),
% 0.21/0.56    inference(resolution,[],[f273,f152])).
% 0.21/0.56  fof(f152,plain,(
% 0.21/0.56    ( ! [X8,X9] : (~r1_lattices(sK0,X8,X9) | ~m1_subset_1(X9,u1_struct_0(sK0)) | k1_lattices(sK0,X8,X9) = X9 | ~m1_subset_1(X8,u1_struct_0(sK0))) ) | (spl4_1 | ~spl4_15)),
% 0.21/0.56    inference(subsumption_resolution,[],[f86,f146])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X8,X9] : (~l2_lattices(sK0) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,u1_struct_0(sK0)) | k1_lattices(sK0,X8,X9) = X9 | ~r1_lattices(sK0,X8,X9)) ) | spl4_1),
% 0.21/0.56    inference(resolution,[],[f60,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 0.21/0.56  fof(f273,plain,(
% 0.21/0.56    r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | ~spl4_24),
% 0.21/0.56    inference(avatar_component_clause,[],[f271])).
% 0.21/0.56  fof(f380,plain,(
% 0.21/0.56    spl4_28 | spl4_1 | ~spl4_7 | ~spl4_13 | ~spl4_15 | ~spl4_23),
% 0.21/0.56    inference(avatar_split_clause,[],[f260,f246,f145,f129,f97,f58,f377])).
% 0.21/0.56  fof(f246,plain,(
% 0.21/0.56    spl4_23 <=> r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.56  fof(f260,plain,(
% 0.21/0.56    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | (spl4_1 | ~spl4_7 | ~spl4_13 | ~spl4_15 | ~spl4_23)),
% 0.21/0.56    inference(subsumption_resolution,[],[f259,f131])).
% 0.21/0.56  fof(f259,plain,(
% 0.21/0.56    sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl4_1 | ~spl4_7 | ~spl4_15 | ~spl4_23)),
% 0.21/0.56    inference(subsumption_resolution,[],[f258,f99])).
% 0.21/0.56  fof(f258,plain,(
% 0.21/0.56    ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK2 = k1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | ~m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | (spl4_1 | ~spl4_15 | ~spl4_23)),
% 0.21/0.56    inference(resolution,[],[f248,f152])).
% 0.21/0.56  fof(f248,plain,(
% 0.21/0.56    r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | ~spl4_23),
% 0.21/0.56    inference(avatar_component_clause,[],[f246])).
% 0.21/0.56  fof(f274,plain,(
% 0.21/0.56    spl4_24 | ~spl4_6 | ~spl4_8 | ~spl4_19 | ~spl4_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f227,f205,f195,f102,f92,f271])).
% 0.21/0.56  fof(f195,plain,(
% 0.21/0.56    spl4_19 <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.56  fof(f205,plain,(
% 0.21/0.56    spl4_20 <=> ! [X11,X10] : (~m1_subset_1(X10,u1_struct_0(sK0)) | r1_lattices(sK0,k4_lattices(sK0,X10,X11),X10) | ~m1_subset_1(X11,u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.56  fof(f227,plain,(
% 0.21/0.56    r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | (~spl4_6 | ~spl4_8 | ~spl4_19 | ~spl4_20)),
% 0.21/0.56    inference(subsumption_resolution,[],[f226,f104])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl4_6 | ~spl4_19 | ~spl4_20)),
% 0.21/0.56    inference(subsumption_resolution,[],[f220,f94])).
% 0.21/0.56  fof(f220,plain,(
% 0.21/0.56    r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK3) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl4_19 | ~spl4_20)),
% 0.21/0.56    inference(superposition,[],[f206,f197])).
% 0.21/0.56  fof(f197,plain,(
% 0.21/0.56    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1) | ~spl4_19),
% 0.21/0.56    inference(avatar_component_clause,[],[f195])).
% 0.21/0.56  fof(f206,plain,(
% 0.21/0.56    ( ! [X10,X11] : (r1_lattices(sK0,k4_lattices(sK0,X10,X11),X10) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0))) ) | ~spl4_20),
% 0.21/0.56    inference(avatar_component_clause,[],[f205])).
% 0.21/0.56  fof(f249,plain,(
% 0.21/0.56    spl4_23 | ~spl4_7 | ~spl4_8 | ~spl4_18 | ~spl4_20),
% 0.21/0.56    inference(avatar_split_clause,[],[f225,f205,f187,f102,f97,f246])).
% 0.21/0.56  fof(f187,plain,(
% 0.21/0.56    spl4_18 <=> k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.56  fof(f225,plain,(
% 0.21/0.56    r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | (~spl4_7 | ~spl4_8 | ~spl4_18 | ~spl4_20)),
% 0.21/0.56    inference(subsumption_resolution,[],[f224,f104])).
% 0.21/0.56  fof(f224,plain,(
% 0.21/0.56    r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl4_7 | ~spl4_18 | ~spl4_20)),
% 0.21/0.56    inference(subsumption_resolution,[],[f219,f99])).
% 0.21/0.56  fof(f219,plain,(
% 0.21/0.56    r1_lattices(sK0,k4_lattices(sK0,sK1,sK2),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl4_18 | ~spl4_20)),
% 0.21/0.56    inference(superposition,[],[f206,f189])).
% 0.21/0.56  fof(f189,plain,(
% 0.21/0.56    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) | ~spl4_18),
% 0.21/0.56    inference(avatar_component_clause,[],[f187])).
% 0.21/0.56  fof(f216,plain,(
% 0.21/0.56    spl4_1 | ~spl4_2 | ~spl4_4 | spl4_21),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f215])).
% 0.21/0.56  fof(f215,plain,(
% 0.21/0.56    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_21)),
% 0.21/0.56    inference(subsumption_resolution,[],[f214,f75])).
% 0.21/0.56  fof(f214,plain,(
% 0.21/0.56    ~l3_lattices(sK0) | (spl4_1 | ~spl4_2 | spl4_21)),
% 0.21/0.56    inference(subsumption_resolution,[],[f213,f65])).
% 0.21/0.56  fof(f213,plain,(
% 0.21/0.56    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl4_1 | spl4_21)),
% 0.21/0.56    inference(subsumption_resolution,[],[f212,f60])).
% 0.21/0.56  fof(f212,plain,(
% 0.21/0.56    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl4_21),
% 0.21/0.56    inference(resolution,[],[f210,f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.56    inference(flattening,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.56  fof(f210,plain,(
% 0.21/0.56    ~v8_lattices(sK0) | spl4_21),
% 0.21/0.56    inference(avatar_component_clause,[],[f208])).
% 0.21/0.56  fof(f208,plain,(
% 0.21/0.56    spl4_21 <=> v8_lattices(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.56  fof(f211,plain,(
% 0.21/0.56    spl4_20 | ~spl4_21 | spl4_1 | ~spl4_4 | ~spl4_12),
% 0.21/0.56    inference(avatar_split_clause,[],[f202,f125,f73,f58,f208,f205])).
% 0.21/0.56  fof(f125,plain,(
% 0.21/0.56    spl4_12 <=> v6_lattices(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.56  fof(f202,plain,(
% 0.21/0.56    ( ! [X10,X11] : (~v8_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | r1_lattices(sK0,k4_lattices(sK0,X10,X11),X10)) ) | (spl4_1 | ~spl4_4 | ~spl4_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f201,f75])).
% 0.21/0.56  fof(f201,plain,(
% 0.21/0.56    ( ! [X10,X11] : (~v8_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | r1_lattices(sK0,k4_lattices(sK0,X10,X11),X10)) ) | (spl4_1 | ~spl4_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f87,f126])).
% 0.21/0.56  fof(f126,plain,(
% 0.21/0.56    v6_lattices(sK0) | ~spl4_12),
% 0.21/0.56    inference(avatar_component_clause,[],[f125])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X10,X11] : (~v6_lattices(sK0) | ~v8_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | r1_lattices(sK0,k4_lattices(sK0,X10,X11),X10)) ) | spl4_1),
% 0.21/0.56    inference(resolution,[],[f60,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~v8_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,k4_lattices(X0,X1,X2),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattices)).
% 0.21/0.56  fof(f198,plain,(
% 0.21/0.56    spl4_19 | spl4_1 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_11 | ~spl4_12),
% 0.21/0.56    inference(avatar_split_clause,[],[f171,f125,f121,f107,f102,f92,f58,f195])).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    spl4_11 <=> l1_lattices(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.56  fof(f171,plain,(
% 0.21/0.56    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK3,sK1) | (spl4_1 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_11 | ~spl4_12)),
% 0.21/0.56    inference(forward_demodulation,[],[f167,f109])).
% 0.21/0.56  fof(f167,plain,(
% 0.21/0.56    k4_lattices(sK0,sK1,sK3) = k4_lattices(sK0,sK3,sK1) | (spl4_1 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12)),
% 0.21/0.56    inference(resolution,[],[f157,f94])).
% 0.21/0.56  fof(f157,plain,(
% 0.21/0.56    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k4_lattices(sK0,sK1,X4) = k4_lattices(sK0,X4,sK1)) ) | (spl4_1 | ~spl4_8 | ~spl4_11 | ~spl4_12)),
% 0.21/0.56    inference(resolution,[],[f154,f104])).
% 0.21/0.56  fof(f154,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)) ) | (spl4_1 | ~spl4_11 | ~spl4_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f153,f122])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    l1_lattices(sK0) | ~spl4_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f121])).
% 0.21/0.56  fof(f153,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)) ) | (spl4_1 | ~spl4_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f82,f126])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)) ) | spl4_1),
% 0.21/0.56    inference(resolution,[],[f60,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v6_lattices(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 0.21/0.56  fof(f190,plain,(
% 0.21/0.56    spl4_18 | spl4_1 | ~spl4_7 | ~spl4_8 | ~spl4_11 | ~spl4_12),
% 0.21/0.56    inference(avatar_split_clause,[],[f166,f125,f121,f102,f97,f58,f187])).
% 0.21/0.56  fof(f166,plain,(
% 0.21/0.56    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1) | (spl4_1 | ~spl4_7 | ~spl4_8 | ~spl4_11 | ~spl4_12)),
% 0.21/0.56    inference(resolution,[],[f157,f99])).
% 0.21/0.56  fof(f185,plain,(
% 0.21/0.56    spl4_1 | ~spl4_2 | ~spl4_4 | spl4_17),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f184])).
% 0.21/0.56  fof(f184,plain,(
% 0.21/0.56    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_17)),
% 0.21/0.56    inference(subsumption_resolution,[],[f183,f75])).
% 0.21/0.56  fof(f183,plain,(
% 0.21/0.56    ~l3_lattices(sK0) | (spl4_1 | ~spl4_2 | spl4_17)),
% 0.21/0.56    inference(subsumption_resolution,[],[f182,f65])).
% 0.21/0.56  fof(f182,plain,(
% 0.21/0.56    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl4_1 | spl4_17)),
% 0.21/0.56    inference(subsumption_resolution,[],[f181,f60])).
% 0.21/0.56  fof(f181,plain,(
% 0.21/0.56    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl4_17),
% 0.21/0.56    inference(resolution,[],[f179,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X0] : (v4_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    ~v4_lattices(sK0) | spl4_17),
% 0.21/0.56    inference(avatar_component_clause,[],[f177])).
% 0.21/0.56  fof(f180,plain,(
% 0.21/0.56    spl4_16 | ~spl4_17 | spl4_1 | ~spl4_15),
% 0.21/0.56    inference(avatar_split_clause,[],[f172,f145,f58,f177,f174])).
% 0.21/0.56  fof(f172,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~v4_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k3_lattices(sK0,X2,X3) = k3_lattices(sK0,X3,X2)) ) | (spl4_1 | ~spl4_15)),
% 0.21/0.56    inference(subsumption_resolution,[],[f83,f146])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~v4_lattices(sK0) | ~l2_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k3_lattices(sK0,X2,X3) = k3_lattices(sK0,X3,X2)) ) | spl4_1),
% 0.21/0.56    inference(resolution,[],[f60,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v4_lattices(X0) | ~l2_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).
% 0.21/0.56  fof(f151,plain,(
% 0.21/0.56    ~spl4_4 | spl4_15),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f150])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    $false | (~spl4_4 | spl4_15)),
% 0.21/0.56    inference(subsumption_resolution,[],[f149,f75])).
% 0.21/0.56  fof(f149,plain,(
% 0.21/0.56    ~l3_lattices(sK0) | spl4_15),
% 0.21/0.56    inference(resolution,[],[f147,f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.56  fof(f147,plain,(
% 0.21/0.56    ~l2_lattices(sK0) | spl4_15),
% 0.21/0.56    inference(avatar_component_clause,[],[f145])).
% 0.21/0.56  fof(f140,plain,(
% 0.21/0.56    spl4_1 | ~spl4_2 | ~spl4_4 | spl4_12),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f139])).
% 0.21/0.56  fof(f139,plain,(
% 0.21/0.56    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f138,f75])).
% 0.21/0.56  fof(f138,plain,(
% 0.21/0.56    ~l3_lattices(sK0) | (spl4_1 | ~spl4_2 | spl4_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f137,f65])).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl4_1 | spl4_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f136,f60])).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl4_12),
% 0.21/0.56    inference(resolution,[],[f127,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    ~v6_lattices(sK0) | spl4_12),
% 0.21/0.56    inference(avatar_component_clause,[],[f125])).
% 0.21/0.56  fof(f135,plain,(
% 0.21/0.56    ~spl4_4 | spl4_11),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f134])).
% 0.21/0.56  fof(f134,plain,(
% 0.21/0.56    $false | (~spl4_4 | spl4_11)),
% 0.21/0.56    inference(subsumption_resolution,[],[f133,f75])).
% 0.21/0.56  fof(f133,plain,(
% 0.21/0.56    ~l3_lattices(sK0) | spl4_11),
% 0.21/0.56    inference(resolution,[],[f123,f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    ~l1_lattices(sK0) | spl4_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f121])).
% 0.21/0.56  fof(f132,plain,(
% 0.21/0.56    ~spl4_11 | ~spl4_12 | spl4_13 | spl4_1 | ~spl4_6 | ~spl4_8 | ~spl4_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f119,f107,f102,f92,f58,f129,f125,f121])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | (spl4_1 | ~spl4_6 | ~spl4_8 | ~spl4_9)),
% 0.21/0.56    inference(subsumption_resolution,[],[f118,f60])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl4_6 | ~spl4_8 | ~spl4_9)),
% 0.21/0.56    inference(subsumption_resolution,[],[f117,f94])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl4_8 | ~spl4_9)),
% 0.21/0.56    inference(subsumption_resolution,[],[f116,f104])).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl4_9),
% 0.21/0.56    inference(superposition,[],[f55,f109])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattices)).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    spl4_10),
% 0.21/0.56    inference(avatar_split_clause,[],[f33,f112])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    k3_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (X2 != X3 & k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((X2 != X3 & (k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.21/0.56    inference(negated_conjecture,[],[f10])).
% 0.21/0.56  fof(f10,conjecture,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v11_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((k3_lattices(X0,X1,X2) = k3_lattices(X0,X1,X3) & k4_lattices(X0,X1,X2) = k4_lattices(X0,X1,X3)) => X2 = X3)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_lattices)).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    spl4_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f32,f107])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK1,sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    spl4_8),
% 0.21/0.56    inference(avatar_split_clause,[],[f36,f102])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    spl4_7),
% 0.21/0.56    inference(avatar_split_clause,[],[f35,f97])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    spl4_6),
% 0.21/0.56    inference(avatar_split_clause,[],[f31,f92])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ~spl4_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f34,f78])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    sK2 != sK3),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    spl4_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f40,f73])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    l3_lattices(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    spl4_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f39,f68])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    v11_lattices(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    spl4_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f38,f63])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    v10_lattices(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ~spl4_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f37,f58])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ~v2_struct_0(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (27656)------------------------------
% 0.21/0.56  % (27656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (27656)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (27656)Memory used [KB]: 11897
% 0.21/0.56  % (27656)Time elapsed: 0.138 s
% 0.21/0.56  % (27656)------------------------------
% 0.21/0.56  % (27656)------------------------------
% 0.21/0.57  % (27652)Success in time 0.204 s
%------------------------------------------------------------------------------
