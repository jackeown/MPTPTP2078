%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:49 EST 2020

% Result     : Theorem 5.81s
% Output     : Refutation 5.81s
% Verified   : 
% Statistics : Number of formulae       : 1049 (9522 expanded)
%              Number of leaves         :  156 (3097 expanded)
%              Depth                    :   40
%              Number of atoms          : 6401 (43184 expanded)
%              Number of equality atoms :  423 (4195 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :   11 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9767,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f111,f116,f128,f178,f186,f214,f277,f338,f349,f354,f419,f424,f427,f447,f702,f814,f840,f979,f984,f986,f1039,f1080,f1243,f1289,f1331,f1337,f1364,f1398,f1407,f1416,f1445,f1490,f1528,f1557,f1607,f1616,f1829,f1927,f2063,f2170,f2403,f2412,f2421,f2430,f2435,f2440,f2445,f2549,f2674,f2685,f2708,f2791,f2798,f2802,f2805,f2924,f2999,f3032,f3289,f3357,f3362,f3367,f3524,f3541,f3548,f3551,f3562,f3575,f3582,f3585,f3596,f3666,f3676,f3691,f3696,f3707,f3722,f3928,f3942,f3952,f3959,f4010,f4024,f4034,f4041,f4053,f4122,f4134,f4179,f4191,f4227,f4244,f4259,f4409,f4829,f4894,f4912,f4924,f4997,f5065,f5076,f5106,f6108,f6266,f6275,f6280,f6285,f6294,f6303,f6333,f6340,f6433,f6453,f6634,f6876,f7027,f7032,f7056,f7098,f7279,f7393,f7432,f7518,f7932,f8801,f8838,f9525,f9659,f9671,f9686,f9703,f9725,f9763])).

fof(f9763,plain,
    ( spl9_1
    | ~ spl9_4
    | spl9_5
    | ~ spl9_6
    | ~ spl9_137 ),
    inference(avatar_contradiction_clause,[],[f9762])).

fof(f9762,plain,
    ( $false
    | spl9_1
    | ~ spl9_4
    | spl9_5
    | ~ spl9_6
    | ~ spl9_137 ),
    inference(subsumption_resolution,[],[f9754,f123])).

fof(f123,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl9_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f9754,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_137 ),
    inference(backward_demodulation,[],[f8800,f9384])).

fof(f9384,plain,
    ( ! [X2] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f9383,f115])).

fof(f115,plain,
    ( l3_lattices(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl9_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f9383,plain,
    ( ! [X2] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
        | ~ l3_lattices(sK0) )
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f9350,f100])).

fof(f100,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl9_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f9350,plain,
    ( ! [X2] :
        ( v2_struct_0(sK0)
        | k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))
        | ~ l3_lattices(sK0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f126,f479])).

fof(f479,plain,(
    ! [X2,X1] :
      ( ~ v13_lattices(X1)
      | v2_struct_0(X1)
      | k5_lattices(X1) = k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1))
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f477,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f477,plain,(
    ! [X2,X1] :
      ( ~ l1_lattices(X1)
      | ~ v13_lattices(X1)
      | v2_struct_0(X1)
      | k5_lattices(X1) = k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1))
      | ~ l3_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f463])).

fof(f463,plain,(
    ! [X2,X1] :
      ( ~ l1_lattices(X1)
      | ~ v13_lattices(X1)
      | v2_struct_0(X1)
      | k5_lattices(X1) = k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f461,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f461,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | v2_struct_0(X0)
      | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0)) ) ),
    inference(subsumption_resolution,[],[f92,f60])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f92,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X2,X1) = X1
      | k5_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f126,plain,
    ( v13_lattices(sK0)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl9_6
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f8800,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl9_137 ),
    inference(avatar_component_clause,[],[f8798])).

fof(f8798,plain,
    ( spl9_137
  <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_137])])).

fof(f9725,plain,
    ( ~ spl9_17
    | spl9_141
    | spl9_1
    | ~ spl9_6
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f9720,f1240,f125,f98,f9722,f416])).

fof(f416,plain,
    ( spl9_17
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f9722,plain,
    ( spl9_141
  <=> k5_lattices(sK0) = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_141])])).

fof(f1240,plain,
    ( spl9_26
  <=> sK2(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f9720,plain,
    ( k5_lattices(sK0) = sK2(sK0)
    | ~ l1_lattices(sK0)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f9382,f1242])).

fof(f1242,plain,
    ( sK2(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f1240])).

fof(f9382,plain,
    ( ~ l1_lattices(sK0)
    | k5_lattices(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f9348,f100])).

fof(f9348,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0))
    | ~ spl9_6 ),
    inference(resolution,[],[f126,f475])).

fof(f475,plain,(
    ! [X5] :
      ( ~ v13_lattices(X5)
      | ~ l1_lattices(X5)
      | v2_struct_0(X5)
      | k5_lattices(X5) = k2_lattices(X5,sK2(X5),k5_lattices(X5)) ) ),
    inference(duplicate_literal_removal,[],[f465])).

fof(f465,plain,(
    ! [X5] :
      ( ~ l1_lattices(X5)
      | ~ v13_lattices(X5)
      | v2_struct_0(X5)
      | k5_lattices(X5) = k2_lattices(X5,sK2(X5),k5_lattices(X5))
      | ~ l1_lattices(X5)
      | v2_struct_0(X5)
      | ~ v13_lattices(X5) ) ),
    inference(resolution,[],[f461,f69])).

fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(f9703,plain,
    ( ~ spl9_17
    | spl9_140
    | spl9_1
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f9377,f125,f98,f9700,f416])).

fof(f9700,plain,
    ( spl9_140
  <=> sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_140])])).

fof(f9377,plain,
    ( sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0))
    | ~ l1_lattices(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f9343,f100])).

fof(f9343,plain,
    ( v2_struct_0(sK0)
    | sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0))
    | ~ l1_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f126,f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v13_lattices(X0)
      | v2_struct_0(X0)
      | sK2(X0) = k2_lattices(X0,k5_lattices(X0),sK2(X0))
      | ~ l1_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,(
    ! [X0] :
      ( ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | sK2(X0) = k2_lattices(X0,k5_lattices(X0),sK2(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f66,f60])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | sK2(X0) = k2_lattices(X0,X2,sK2(X0))
      | ~ v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9686,plain,
    ( ~ spl9_139
    | ~ spl9_57
    | spl9_127 ),
    inference(avatar_split_clause,[],[f9674,f7024,f2546,f9683])).

fof(f9683,plain,
    ( spl9_139
  <=> k5_lattices(sK0) = sK3(sK0,k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_139])])).

fof(f2546,plain,
    ( spl9_57
  <=> k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f7024,plain,
    ( spl9_127
  <=> sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).

fof(f9674,plain,
    ( k5_lattices(sK0) != sK3(sK0,k5_lattices(sK0))
    | ~ spl9_57
    | spl9_127 ),
    inference(backward_demodulation,[],[f7026,f2547])).

fof(f2547,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_57 ),
    inference(avatar_component_clause,[],[f2546])).

fof(f7026,plain,
    ( sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | spl9_127 ),
    inference(avatar_component_clause,[],[f7024])).

fof(f9671,plain,
    ( spl9_138
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f9637,f811,f274,f113,f108,f103,f98,f9668])).

fof(f9668,plain,
    ( spl9_138
  <=> r1_lattices(sK0,sK2(sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_138])])).

fof(f103,plain,
    ( spl9_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f108,plain,
    ( spl9_3
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f274,plain,
    ( spl9_10
  <=> sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f811,plain,
    ( spl9_20
  <=> m1_subset_1(sK2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f9637,plain,
    ( r1_lattices(sK0,sK2(sK0),sK2(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f9599,f813])).

fof(f813,plain,
    ( m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f811])).

fof(f9599,plain,
    ( r1_lattices(sK0,sK2(sK0),sK2(sK0))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(superposition,[],[f4369,f276])).

fof(f276,plain,
    ( sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f274])).

fof(f4369,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f4359])).

fof(f4359,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f4343,f3280])).

fof(f3280,plain,
    ( ! [X4,X3] :
        ( ~ r3_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3279,f100])).

fof(f3279,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3278,f115])).

fof(f3278,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | ~ l3_lattices(sK0)
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3277,f110])).

fof(f110,plain,
    ( v4_lattice3(sK0)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f3277,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3276,f105])).

fof(f105,plain,
    ( v10_lattices(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f3276,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f3267])).

fof(f3267,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X3),X4)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f3088,f96])).

fof(f96,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,a_2_4_lattice3(X1,X2))
      | ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r3_lattices(X1,X2,X3)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ r3_lattices(X1,X2,X3)
      | r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).

fof(f3088,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X1),X2) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3087,f110])).

fof(f3087,plain,
    ( ! [X2,X1] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X1),X2)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | ~ v4_lattice3(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3086,f105])).

fof(f3086,plain,
    ( ! [X2,X1] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X1),X2)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3085,f100])).

fof(f3085,plain,
    ( ! [X2,X1] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X1),X2)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | v2_struct_0(sK0)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3073,f115])).

fof(f3073,plain,
    ( ! [X2,X1] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X1),X2)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f453,f281])).

fof(f281,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f280,f100])).

fof(f280,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X0))) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f279,f115])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X0))) )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f278,f105])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ v10_lattices(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X0))) )
    | ~ spl9_3 ),
    inference(resolution,[],[f201,f110])).

fof(f201,plain,(
    ! [X2,X1] :
      ( ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_4_lattice3(X1,k15_lattice3(X1,X2))) ) ),
    inference(duplicate_literal_removal,[],[f191])).

fof(f191,plain,(
    ! [X2,X1] :
      ( ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_4_lattice3(X1,k15_lattice3(X1,X2)))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f75,f87])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

fof(f453,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k16_lattice3(X0,X1),X2)
      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0) ) ),
    inference(duplicate_literal_removal,[],[f449])).

fof(f449,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | r1_lattices(X0,k16_lattice3(X0,X1),X2)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f83,f94])).

fof(f94,plain,(
    ! [X2,X0] :
      ( r3_lattice3(X0,k16_lattice3(X0,X2),X2)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X0,X1,X2)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X2)
      | r1_lattices(X0,X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(f4343,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f4324])).

fof(f4324,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f3877,f333])).

fof(f333,plain,
    ( ! [X0] :
        ( r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f332,f100])).

fof(f332,plain,
    ( ! [X0] :
        ( r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f331,f115])).

fof(f331,plain,
    ( ! [X0] :
        ( r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f330,f110])).

fof(f330,plain,
    ( ! [X0] :
        ( r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f324,f105])).

fof(f324,plain,
    ( ! [X0] :
        ( r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f94,f281])).

fof(f3877,plain,
    ( ! [X2,X1] :
        ( ~ r3_lattice3(sK0,X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_lattices(sK0,X2,k15_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3876,f100])).

fof(f3876,plain,
    ( ! [X2,X1] :
        ( r3_lattices(sK0,X2,k15_lattice3(sK0,X1))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3875,f115])).

fof(f3875,plain,
    ( ! [X2,X1] :
        ( r3_lattices(sK0,X2,k15_lattice3(sK0,X1))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3874,f110])).

fof(f3874,plain,
    ( ! [X2,X1] :
        ( r3_lattices(sK0,X2,k15_lattice3(sK0,X1))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3836,f105])).

fof(f3836,plain,
    ( ! [X2,X1] :
        ( r3_lattices(sK0,X2,k15_lattice3(sK0,X1))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f95,f281])).

fof(f95,plain,(
    ! [X2,X0,X3] :
      ( r3_lattices(X0,X3,k16_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X3,X2)
      | r3_lattices(X0,X3,X1)
      | k16_lattice3(X0,X2) != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9659,plain,
    ( spl9_31
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f9636,f811,f274,f113,f108,f103,f98,f1395])).

fof(f1395,plain,
    ( spl9_31
  <=> r3_lattices(sK0,sK2(sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f9636,plain,
    ( r3_lattices(sK0,sK2(sK0),sK2(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f9598,f813])).

fof(f9598,plain,
    ( r3_lattices(sK0,sK2(sK0),sK2(sK0))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(superposition,[],[f4343,f276])).

fof(f9525,plain,
    ( ~ spl9_17
    | spl9_1
    | ~ spl9_6
    | ~ spl9_25
    | spl9_57 ),
    inference(avatar_split_clause,[],[f9524,f2546,f1077,f125,f98,f416])).

fof(f1077,plain,
    ( spl9_25
  <=> m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f9524,plain,
    ( ~ l1_lattices(sK0)
    | spl9_1
    | ~ spl9_6
    | ~ spl9_25
    | spl9_57 ),
    inference(subsumption_resolution,[],[f9289,f126])).

fof(f9289,plain,
    ( ~ l1_lattices(sK0)
    | ~ v13_lattices(sK0)
    | spl9_1
    | ~ spl9_25
    | spl9_57 ),
    inference(subsumption_resolution,[],[f9288,f2548])).

fof(f2548,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | spl9_57 ),
    inference(avatar_component_clause,[],[f2546])).

fof(f9288,plain,
    ( ~ l1_lattices(sK0)
    | ~ v13_lattices(sK0)
    | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1265,f100])).

fof(f1265,plain,
    ( ~ l1_lattices(sK0)
    | ~ v13_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_25 ),
    inference(resolution,[],[f1079,f481])).

fof(f481,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | v2_struct_0(X0)
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X2) ) ),
    inference(subsumption_resolution,[],[f93,f60])).

fof(f93,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X2) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | k5_lattices(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1079,plain,
    ( m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ spl9_25 ),
    inference(avatar_component_clause,[],[f1077])).

fof(f8838,plain,
    ( ~ spl9_62
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_102 ),
    inference(avatar_split_clause,[],[f8834,f4892,f125,f113,f108,f103,f98,f2784])).

fof(f2784,plain,
    ( spl9_62
  <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f4892,plain,
    ( spl9_102
  <=> ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).

fof(f8834,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_102 ),
    inference(trivial_inequality_removal,[],[f8831])).

fof(f8831,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_102 ),
    inference(superposition,[],[f4893,f8788])).

fof(f8788,plain,
    ( ! [X3] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X3)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f8779,f1686])).

fof(f1686,plain,
    ( ! [X0] : sK3(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f1685,f127])).

fof(f127,plain,
    ( ~ v13_lattices(sK0)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1685,plain,
    ( ! [X0] :
        ( sK3(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0))))
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1684,f105])).

fof(f1684,plain,
    ( ! [X0] :
        ( sK3(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0))))
        | ~ v10_lattices(sK0)
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1683,f100])).

fof(f1683,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | sK3(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0))))
        | ~ v10_lattices(sK0)
        | v13_lattices(sK0) )
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1682,f115])).

fof(f1682,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | sK3(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0))))
        | ~ v10_lattices(sK0)
        | v13_lattices(sK0) )
    | ~ spl9_3 ),
    inference(resolution,[],[f1026,f110])).

fof(f1026,plain,(
    ! [X2,X1] :
      ( ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | sK3(X1,k15_lattice3(X1,X2)) = k15_lattice3(X1,a_2_3_lattice3(X1,sK3(X1,k15_lattice3(X1,X2))))
      | ~ v10_lattices(X1)
      | v13_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f1010])).

fof(f1010,plain,(
    ! [X2,X1] :
      ( ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | sK3(X1,k15_lattice3(X1,X2)) = k15_lattice3(X1,a_2_3_lattice3(X1,sK3(X1,k15_lattice3(X1,X2))))
      | ~ v10_lattices(X1)
      | v13_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f169,f87])).

fof(f169,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ v4_lattice3(X4)
      | ~ l3_lattices(X4)
      | v2_struct_0(X4)
      | sK3(X4,X5) = k15_lattice3(X4,a_2_3_lattice3(X4,sK3(X4,X5)))
      | ~ v10_lattices(X4)
      | v13_lattices(X4) ) ),
    inference(subsumption_resolution,[],[f163,f50])).

fof(f163,plain,(
    ! [X4,X5] :
      ( ~ v10_lattices(X4)
      | ~ v4_lattice3(X4)
      | ~ l3_lattices(X4)
      | v2_struct_0(X4)
      | sK3(X4,X5) = k15_lattice3(X4,a_2_3_lattice3(X4,sK3(X4,X5)))
      | ~ l1_lattices(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | v13_lattices(X4) ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X4,X5] :
      ( ~ v10_lattices(X4)
      | ~ v4_lattice3(X4)
      | ~ l3_lattices(X4)
      | v2_struct_0(X4)
      | sK3(X4,X5) = k15_lattice3(X4,a_2_3_lattice3(X4,sK3(X4,X5)))
      | ~ l1_lattices(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | v2_struct_0(X4)
      | v13_lattices(X4) ) ),
    inference(resolution,[],[f74,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8779,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f8771,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f8771,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f8770,f100])).

fof(f8770,plain,
    ( ! [X0,X1] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ r1_tarski(X0,X1)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f8760,f115])).

fof(f8760,plain,
    ( ! [X0,X1] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ r1_tarski(X0,X1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f8750,f87])).

fof(f8750,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ r1_tarski(X0,X1) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f8749,f100])).

fof(f8749,plain,
    ( ! [X0,X1] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r1_tarski(X0,X1)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f8739,f115])).

fof(f8739,plain,
    ( ! [X0,X1] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r1_tarski(X0,X1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f7971,f87])).

fof(f7971,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X7),u1_struct_0(sK0))
        | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
        | ~ m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0))
        | ~ r1_tarski(X6,X7) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7970,f100])).

fof(f7970,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0))
        | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
        | ~ m1_subset_1(k15_lattice3(sK0,X7),u1_struct_0(sK0))
        | ~ r1_tarski(X6,X7)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7969,f115])).

fof(f7969,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0))
        | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
        | ~ m1_subset_1(k15_lattice3(sK0,X7),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X6,X7)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7968,f110])).

fof(f7968,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0))
        | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
        | ~ m1_subset_1(k15_lattice3(sK0,X7),u1_struct_0(sK0))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X6,X7)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7940,f105])).

fof(f7940,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0))
        | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7))
        | ~ m1_subset_1(k15_lattice3(sK0,X7),u1_struct_0(sK0))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X6,X7)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f7918,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ r1_tarski(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
            & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).

fof(f7918,plain,
    ( ! [X0,X1] :
        ( ~ r3_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7917,f100])).

fof(f7917,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7916,f115])).

fof(f7916,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ l3_lattices(sK0)
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7915,f110])).

fof(f7915,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7914,f105])).

fof(f7914,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f7899])).

fof(f7899,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f7734,f96])).

fof(f7734,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X2) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7733,f110])).

fof(f7733,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | ~ v4_lattice3(sK0)
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X2) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7732,f105])).

fof(f7732,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X2) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7731,f100])).

fof(f7731,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | v2_struct_0(sK0)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X2) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f7717,f115])).

fof(f7717,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X2) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f3084,f281])).

fof(f3084,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k16_lattice3(X3,X4),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ v4_lattice3(X3)
      | k16_lattice3(X3,X4) = k2_lattices(X3,k16_lattice3(X3,X4),X5) ) ),
    inference(subsumption_resolution,[],[f3083,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f3083,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k16_lattice3(X3,X4),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v8_lattices(X3)
      | k16_lattice3(X3,X4) = k2_lattices(X3,k16_lattice3(X3,X4),X5) ) ),
    inference(subsumption_resolution,[],[f3080,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3080,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k16_lattice3(X3,X4),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v8_lattices(X3)
      | ~ v9_lattices(X3)
      | k16_lattice3(X3,X4) = k2_lattices(X3,k16_lattice3(X3,X4),X5) ) ),
    inference(duplicate_literal_removal,[],[f3071])).

fof(f3071,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k16_lattice3(X3,X4),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r2_hidden(X5,X4)
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v8_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ l3_lattices(X3)
      | ~ m1_subset_1(k16_lattice3(X3,X4),u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | k16_lattice3(X3,X4) = k2_lattices(X3,k16_lattice3(X3,X4),X5)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f453,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f4893,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl9_102 ),
    inference(avatar_component_clause,[],[f4892])).

fof(f8801,plain,
    ( spl9_137
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f8780,f175,f113,f108,f103,f98,f8798])).

fof(f175,plain,
    ( spl9_7
  <=> k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f8780,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(superposition,[],[f8779,f177])).

fof(f177,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f175])).

fof(f7932,plain,
    ( spl9_136
    | ~ spl9_62
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42
    | ~ spl9_122 ),
    inference(avatar_split_clause,[],[f7921,f6330,f1826,f113,f108,f103,f98,f2784,f7929])).

fof(f7929,plain,
    ( spl9_136
  <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f1826,plain,
    ( spl9_42
  <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f6330,plain,
    ( spl9_122
  <=> r2_hidden(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).

fof(f7921,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42
    | ~ spl9_122 ),
    inference(subsumption_resolution,[],[f7903,f1828])).

fof(f1828,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f1826])).

fof(f7903,plain,
    ( ~ m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_122 ),
    inference(resolution,[],[f7734,f6331])).

fof(f6331,plain,
    ( r2_hidden(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ spl9_122 ),
    inference(avatar_component_clause,[],[f6330])).

fof(f7518,plain,
    ( ~ spl9_134
    | spl9_135
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_37
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f3977,f1525,f1487,f335,f183,f113,f108,f103,f98,f7515,f7511])).

fof(f7511,plain,
    ( spl9_134
  <=> r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f7515,plain,
    ( spl9_135
  <=> r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).

fof(f183,plain,
    ( spl9_8
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f335,plain,
    ( spl9_11
  <=> r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f1487,plain,
    ( spl9_37
  <=> m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f1525,plain,
    ( spl9_38
  <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f3977,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_37
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f3968,f1489])).

fof(f1489,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f1487])).

fof(f3968,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_38 ),
    inference(superposition,[],[f3853,f1527])).

fof(f1527,plain,
    ( sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f1525])).

fof(f3853,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))
        | ~ r3_lattice3(sK0,k5_lattices(sK0),X0)
        | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f3852,f100])).

fof(f3852,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f3851,f185])).

fof(f185,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f183])).

fof(f3851,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f3850,f115])).

fof(f3850,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f3849,f110])).

fof(f3849,plain,
    ( ! [X0] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f3848,f105])).

fof(f3848,plain,
    ( ! [X0] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(duplicate_literal_removal,[],[f3829])).

fof(f3829,plain,
    ( ! [X0] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))
        | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(resolution,[],[f95,f602])).

fof(f602,plain,
    ( ! [X0] :
        ( ~ r3_lattices(sK0,k5_lattices(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k5_lattices(sK0),X0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f601,f100])).

fof(f601,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k5_lattices(sK0),X0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f600,f185])).

fof(f600,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k5_lattices(sK0),X0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f599,f115])).

fof(f599,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k5_lattices(sK0),X0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f598,f110])).

fof(f598,plain,
    ( ! [X0] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k5_lattices(sK0),X0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f597,f105])).

fof(f597,plain,
    ( ! [X0] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k5_lattices(sK0),X0) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(duplicate_literal_removal,[],[f594])).

fof(f594,plain,
    ( ! [X0] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k5_lattices(sK0),X0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k5_lattices(sK0),X0) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(resolution,[],[f96,f456])).

fof(f456,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,k5_lattices(sK0),X3) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f455,f100])).

fof(f455,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | r1_lattices(sK0,k5_lattices(sK0),X3)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f454,f185])).

fof(f454,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | r1_lattices(sK0,k5_lattices(sK0),X3)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f450,f115])).

fof(f450,plain,
    ( ! [X3] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | r1_lattices(sK0,k5_lattices(sK0),X3)
        | v2_struct_0(sK0) )
    | ~ spl9_11 ),
    inference(resolution,[],[f83,f337])).

fof(f337,plain,
    ( r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f335])).

fof(f7432,plain,
    ( ~ spl9_62
    | spl9_133
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42
    | ~ spl9_121 ),
    inference(avatar_split_clause,[],[f7402,f6326,f1826,f113,f108,f103,f98,f7429,f2784])).

fof(f7429,plain,
    ( spl9_133
  <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).

fof(f6326,plain,
    ( spl9_121
  <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).

fof(f7402,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42
    | ~ spl9_121 ),
    inference(subsumption_resolution,[],[f7400,f1828])).

fof(f7400,plain,
    ( ~ m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_121 ),
    inference(resolution,[],[f6328,f3280])).

fof(f6328,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ spl9_121 ),
    inference(avatar_component_clause,[],[f6326])).

fof(f7393,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_64
    | spl9_121 ),
    inference(avatar_contradiction_clause,[],[f7392])).

fof(f7392,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_64
    | spl9_121 ),
    inference(subsumption_resolution,[],[f7380,f49])).

fof(f7380,plain,
    ( ~ r1_tarski(k1_xboole_0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_64
    | spl9_121 ),
    inference(resolution,[],[f2930,f6327])).

fof(f6327,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_121 ),
    inference(avatar_component_clause,[],[f6326])).

fof(f2930,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
        | ~ r1_tarski(X0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_64 ),
    inference(superposition,[],[f264,f2923])).

fof(f2923,plain,
    ( sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f2921])).

fof(f2921,plain,
    ( spl9_64
  <=> sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f264,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X2))
        | ~ r1_tarski(X3,a_2_3_lattice3(sK0,k15_lattice3(sK0,X2))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f263,f100])).

fof(f263,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X2))
        | ~ r1_tarski(X3,a_2_3_lattice3(sK0,k15_lattice3(sK0,X2)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f262,f115])).

fof(f262,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X2))
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X3,a_2_3_lattice3(sK0,k15_lattice3(sK0,X2)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f261,f110])).

fof(f261,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X2))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X3,a_2_3_lattice3(sK0,k15_lattice3(sK0,X2)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f258,f105])).

fof(f258,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X2))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X3,a_2_3_lattice3(sK0,k15_lattice3(sK0,X2)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f81,f253])).

fof(f253,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k15_lattice3(sK0,X0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f252,f100])).

fof(f252,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k15_lattice3(sK0,X0))) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f251,f115])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k15_lattice3(sK0,X0))) )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f250,f105])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ v10_lattices(sK0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k15_lattice3(sK0,X0))) )
    | ~ spl9_3 ),
    inference(resolution,[],[f165,f110])).

fof(f165,plain,(
    ! [X2,X1] :
      ( ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_3_lattice3(X1,k15_lattice3(X1,X2))) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X2,X1] :
      ( ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_3_lattice3(X1,k15_lattice3(X1,X2)))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f74,f87])).

fof(f7279,plain,
    ( spl9_132
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f1956,f1924,f113,f108,f103,f98,f7276])).

fof(f7276,plain,
    ( spl9_132
  <=> sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_132])])).

fof(f1924,plain,
    ( spl9_43
  <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f1956,plain,
    ( sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f1955,f100])).

fof(f1955,plain,
    ( v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f1954,f115])).

fof(f1954,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f1953,f110])).

fof(f1953,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))
    | ~ spl9_2
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f1935,f105])).

fof(f1935,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))
    | ~ spl9_43 ),
    inference(resolution,[],[f1926,f75])).

fof(f1926,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),u1_struct_0(sK0))
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f1924])).

fof(f7098,plain,
    ( spl9_131
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f1952,f1924,f113,f108,f103,f98,f7095])).

fof(f7095,plain,
    ( spl9_131
  <=> sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).

fof(f1952,plain,
    ( sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f1951,f100])).

fof(f1951,plain,
    ( v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f1950,f115])).

fof(f1950,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f1949,f110])).

fof(f1949,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))
    | ~ spl9_2
    | ~ spl9_43 ),
    inference(subsumption_resolution,[],[f1934,f105])).

fof(f1934,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))
    | ~ spl9_43 ),
    inference(resolution,[],[f1926,f74])).

fof(f7056,plain,
    ( spl9_129
    | ~ spl9_130
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_36
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f6804,f1487,f1442,f211,f183,f113,f108,f103,f98,f7053,f7049])).

fof(f7049,plain,
    ( spl9_129
  <=> r1_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).

fof(f7053,plain,
    ( spl9_130
  <=> r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).

fof(f211,plain,
    ( spl9_9
  <=> k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f1442,plain,
    ( spl9_36
  <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f6804,plain,
    ( ~ r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | r1_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_36
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f6784,f1489])).

fof(f6784,plain,
    ( ~ r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | r1_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_36 ),
    inference(superposition,[],[f6767,f1444])).

fof(f1444,plain,
    ( sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f1442])).

fof(f6767,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f6751,f185])).

fof(f6751,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(superposition,[],[f3867,f213])).

fof(f213,plain,
    ( k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f211])).

fof(f3867,plain,
    ( ! [X4,X5] :
        ( r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4))
        | ~ m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k15_lattice3(sK0,X5),X4)
        | ~ m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3866,f100])).

fof(f3866,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k15_lattice3(sK0,X5),X4)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3865,f115])).

fof(f3865,plain,
    ( ! [X4,X5] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k15_lattice3(sK0,X5),X4)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3864,f110])).

fof(f3864,plain,
    ( ! [X4,X5] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k15_lattice3(sK0,X5),X4)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3845,f105])).

fof(f3845,plain,
    ( ! [X4,X5] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k15_lattice3(sK0,X5),X4)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f3832])).

fof(f3832,plain,
    ( ! [X4,X5] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,k15_lattice3(sK0,X5),X4)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0))
        | r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4))
        | ~ m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f95,f3280])).

fof(f7032,plain,
    ( spl9_128
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f2161,f1442,f125,f113,f108,f103,f98,f7029])).

fof(f7029,plain,
    ( spl9_128
  <=> r3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).

fof(f2161,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(superposition,[],[f2055,f1444])).

fof(f2055,plain,
    ( ! [X1] : r3_lattice3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f2041,f1686])).

fof(f2041,plain,
    ( ! [X10] : r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2040,f100])).

fof(f2040,plain,
    ( ! [X10] :
        ( r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10))))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2039,f1732])).

fof(f1732,plain,
    ( ! [X44] : m1_subset_1(sK3(sK0,k15_lattice3(sK0,X44)),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f1731,f100])).

fof(f1731,plain,
    ( ! [X44] :
        ( m1_subset_1(sK3(sK0,k15_lattice3(sK0,X44)),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f1722,f115])).

fof(f1722,plain,
    ( ! [X44] :
        ( m1_subset_1(sK3(sK0,k15_lattice3(sK0,X44)),u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f87,f1686])).

fof(f2039,plain,
    ( ! [X10] :
        ( r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10))))
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X10)),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2038,f115])).

fof(f2038,plain,
    ( ! [X10] :
        ( r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10))))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X10)),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2037,f110])).

fof(f2037,plain,
    ( ! [X10] :
        ( r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10))))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X10)),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2034,f105])).

fof(f2034,plain,
    ( ! [X10] :
        ( r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10))))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X10)),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f94,f1701])).

fof(f1701,plain,
    ( ! [X13] : sK3(sK0,k15_lattice3(sK0,X13)) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X13))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f281,f1686])).

fof(f7027,plain,
    ( spl9_107
    | ~ spl9_68
    | ~ spl9_69
    | ~ spl9_127
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_21
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f1580,f1077,f837,f183,f113,f98,f7024,f3350,f3346,f5062])).

fof(f5062,plain,
    ( spl9_107
  <=> r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_107])])).

fof(f3346,plain,
    ( spl9_68
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f3350,plain,
    ( spl9_69
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).

fof(f837,plain,
    ( spl9_21
  <=> k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f1580,plain,
    ( sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_21
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1579,f100])).

fof(f1579,plain,
    ( sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | v2_struct_0(sK0)
    | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0))
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_21
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1578,f185])).

fof(f1578,plain,
    ( sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0))
    | ~ spl9_4
    | ~ spl9_21
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1577,f1079])).

fof(f1577,plain,
    ( sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0))
    | ~ spl9_4
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f1565,f115])).

fof(f1565,plain,
    ( sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0))
    | ~ spl9_21 ),
    inference(superposition,[],[f58,f839])).

fof(f839,plain,
    ( k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f837])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) != X1
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6876,plain,
    ( ~ spl9_17
    | spl9_126
    | spl9_1
    | spl9_6
    | ~ spl9_110 ),
    inference(avatar_split_clause,[],[f6137,f6106,f125,f98,f6874,f416])).

fof(f6874,plain,
    ( spl9_126
  <=> ! [X32,X31] :
        ( k2_lattices(sK0,sK3(sK0,X31),sK3(sK0,k15_lattice3(sK0,X32))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X32)),sK3(sK0,X31))
        | ~ m1_subset_1(X31,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_126])])).

fof(f6106,plain,
    ( spl9_110
  <=> ! [X5,X6] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k2_lattices(sK0,X5,sK3(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X6)),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).

fof(f6137,plain,
    ( ! [X31,X32] :
        ( k2_lattices(sK0,sK3(sK0,X31),sK3(sK0,k15_lattice3(sK0,X32))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X32)),sK3(sK0,X31))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X31,u1_struct_0(sK0)) )
    | spl9_1
    | spl9_6
    | ~ spl9_110 ),
    inference(subsumption_resolution,[],[f6136,f127])).

fof(f6136,plain,
    ( ! [X31,X32] :
        ( k2_lattices(sK0,sK3(sK0,X31),sK3(sK0,k15_lattice3(sK0,X32))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X32)),sK3(sK0,X31))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X31,u1_struct_0(sK0))
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_110 ),
    inference(subsumption_resolution,[],[f6130,f100])).

fof(f6130,plain,
    ( ! [X31,X32] :
        ( k2_lattices(sK0,sK3(sK0,X31),sK3(sK0,k15_lattice3(sK0,X32))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X32)),sK3(sK0,X31))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X31,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | ~ spl9_110 ),
    inference(resolution,[],[f6107,f68])).

fof(f6107,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k2_lattices(sK0,X5,sK3(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X6)),X5) )
    | ~ spl9_110 ),
    inference(avatar_component_clause,[],[f6106])).

fof(f6634,plain,
    ( spl9_125
    | ~ spl9_36
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f4248,f4242,f1442,f6631])).

fof(f6631,plain,
    ( spl9_125
  <=> sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_125])])).

fof(f4242,plain,
    ( spl9_98
  <=> ! [X0] : sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).

fof(f4248,plain,
    ( sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ spl9_36
    | ~ spl9_98 ),
    inference(superposition,[],[f4243,f1444])).

fof(f4243,plain,
    ( ! [X0] : sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))
    | ~ spl9_98 ),
    inference(avatar_component_clause,[],[f4242])).

fof(f6453,plain,
    ( spl9_124
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f2512,f1442,f125,f113,f108,f103,f98,f6450])).

fof(f6450,plain,
    ( spl9_124
  <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f2512,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(superposition,[],[f2304,f1444])).

fof(f2304,plain,
    ( ! [X46] : m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X46)))))))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f1995,f1691])).

fof(f1691,plain,
    ( ! [X1] : sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f1686,f1686])).

fof(f1995,plain,
    ( ! [X1] : m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1)))))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f1897,f1686])).

fof(f1897,plain,
    ( ! [X1] : m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1))))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f1799,f1686])).

fof(f1799,plain,
    ( ! [X1] : m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1)))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f1756,f1686])).

fof(f1756,plain,
    ( ! [X1] : m1_subset_1(sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f1732,f1686])).

fof(f6433,plain,
    ( spl9_123
    | ~ spl9_62
    | ~ spl9_68
    | ~ spl9_69
    | spl9_1
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_77 ),
    inference(avatar_split_clause,[],[f3600,f3593,f1487,f113,f98,f3350,f3346,f2784,f6430])).

fof(f6430,plain,
    ( spl9_123
  <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).

fof(f3593,plain,
    ( spl9_77
  <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).

fof(f3600,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_77 ),
    inference(subsumption_resolution,[],[f3599,f100])).

fof(f3599,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_77 ),
    inference(subsumption_resolution,[],[f3598,f1489])).

fof(f3598,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_77 ),
    inference(subsumption_resolution,[],[f3597,f115])).

fof(f3597,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | v2_struct_0(sK0)
    | ~ spl9_77 ),
    inference(resolution,[],[f3595,f59])).

fof(f3595,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_77 ),
    inference(avatar_component_clause,[],[f3593])).

fof(f6340,plain,
    ( ~ spl9_121
    | ~ spl9_62
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42
    | spl9_122 ),
    inference(avatar_split_clause,[],[f6339,f6330,f1826,f113,f108,f103,f98,f2784,f6326])).

fof(f6339,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42
    | spl9_122 ),
    inference(subsumption_resolution,[],[f6338,f100])).

fof(f6338,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42
    | spl9_122 ),
    inference(subsumption_resolution,[],[f6337,f1828])).

fof(f6337,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_122 ),
    inference(subsumption_resolution,[],[f6336,f115])).

fof(f6336,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | spl9_122 ),
    inference(subsumption_resolution,[],[f6335,f110])).

fof(f6335,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | spl9_122 ),
    inference(subsumption_resolution,[],[f6334,f105])).

fof(f6334,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | v2_struct_0(sK0)
    | spl9_122 ),
    inference(resolution,[],[f6332,f96])).

fof(f6332,plain,
    ( ~ r2_hidden(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | spl9_122 ),
    inference(avatar_component_clause,[],[f6330])).

fof(f6333,plain,
    ( spl9_121
    | ~ spl9_122
    | ~ spl9_64
    | ~ spl9_71 ),
    inference(avatar_split_clause,[],[f3531,f3522,f2921,f6330,f6326])).

fof(f3522,plain,
    ( spl9_71
  <=> ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
        | ~ r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f3531,plain,
    ( ~ r2_hidden(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ spl9_64
    | ~ spl9_71 ),
    inference(superposition,[],[f3523,f2923])).

fof(f3523,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
        | r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) )
    | ~ spl9_71 ),
    inference(avatar_component_clause,[],[f3522])).

fof(f6303,plain,
    ( spl9_119
    | ~ spl9_120
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1470,f1442,f981,f113,f108,f103,f98,f6300,f6296])).

fof(f6296,plain,
    ( spl9_119
  <=> r3_lattices(sK0,sK2(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).

fof(f6300,plain,
    ( spl9_120
  <=> r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).

fof(f981,plain,
    ( spl9_23
  <=> sK2(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f1470,plain,
    ( ~ r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,sK2(sK0)))
    | r3_lattices(sK0,sK2(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23
    | ~ spl9_36 ),
    inference(superposition,[],[f1220,f1444])).

fof(f1220,plain,
    ( ! [X1] :
        ( ~ r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)),a_2_4_lattice3(sK0,sK2(sK0)))
        | r3_lattices(sK0,sK2(sK0),k15_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(superposition,[],[f291,f983])).

fof(f983,plain,
    ( sK2(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK2(sK0)))
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f981])).

fof(f291,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X3),k15_lattice3(sK0,X2))
        | ~ r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X2)),X3) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f290,f100])).

fof(f290,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X3),k15_lattice3(sK0,X2))
        | ~ r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X2)),X3)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f289,f115])).

fof(f289,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X3),k15_lattice3(sK0,X2))
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X2)),X3)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f288,f110])).

fof(f288,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X3),k15_lattice3(sK0,X2))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X2)),X3)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f286,f105])).

fof(f286,plain,
    ( ! [X2,X3] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X3),k15_lattice3(sK0,X2))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X2)),X3)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f82,f281])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ r1_tarski(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6294,plain,
    ( spl9_117
    | ~ spl9_118
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1469,f1442,f981,f113,f108,f103,f98,f6291,f6287])).

fof(f6287,plain,
    ( spl9_117
  <=> r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_117])])).

fof(f6291,plain,
    ( spl9_118
  <=> r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_118])])).

fof(f1469,plain,
    ( ~ r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK2(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23
    | ~ spl9_36 ),
    inference(superposition,[],[f1219,f1444])).

fof(f1219,plain,
    ( ! [X0] :
        ( ~ r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))
        | r3_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(superposition,[],[f295,f983])).

fof(f295,plain,
    ( ! [X4,X5] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X4),k16_lattice3(sK0,X5))
        | ~ r1_tarski(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,X4))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f294,f100])).

fof(f294,plain,
    ( ! [X4,X5] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X4),k16_lattice3(sK0,X5))
        | ~ r1_tarski(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,X4)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f293,f115])).

fof(f293,plain,
    ( ! [X4,X5] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X4),k16_lattice3(sK0,X5))
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,X4)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f292,f110])).

fof(f292,plain,
    ( ! [X4,X5] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X4),k16_lattice3(sK0,X5))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,X4)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f287,f105])).

fof(f287,plain,
    ( ! [X4,X5] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X4),k16_lattice3(sK0,X5))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,X4)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f82,f281])).

fof(f6285,plain,
    ( spl9_114
    | ~ spl9_116
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1463,f1442,f211,f113,f108,f103,f98,f6282,f6272])).

fof(f6272,plain,
    ( spl9_114
  <=> r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).

fof(f6282,plain,
    ( spl9_116
  <=> r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).

fof(f1463,plain,
    ( ~ r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_36 ),
    inference(superposition,[],[f311,f1444])).

fof(f311,plain,
    ( ! [X0] :
        ( ~ r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(superposition,[],[f295,f213])).

fof(f6280,plain,
    ( spl9_112
    | ~ spl9_115
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1460,f1442,f211,f113,f108,f103,f98,f6277,f6263])).

fof(f6263,plain,
    ( spl9_112
  <=> r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_112])])).

fof(f6277,plain,
    ( spl9_115
  <=> r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_115])])).

fof(f1460,plain,
    ( ~ r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_36 ),
    inference(superposition,[],[f305,f1444])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)),a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(superposition,[],[f291,f213])).

fof(f6275,plain,
    ( ~ spl9_113
    | spl9_114
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1447,f1442,f175,f113,f108,f103,f98,f6272,f6268])).

fof(f6268,plain,
    ( spl9_113
  <=> r1_tarski(a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_3_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_113])])).

fof(f1447,plain,
    ( r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | ~ r1_tarski(a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_36 ),
    inference(superposition,[],[f225,f1444])).

fof(f225,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ r1_tarski(X0,a_2_3_lattice3(sK0,k5_lattices(sK0))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f224,f100])).

fof(f224,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ r1_tarski(X0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f223,f115])).

fof(f223,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f222,f110])).

fof(f222,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f217,f105])).

fof(f217,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_7 ),
    inference(superposition,[],[f81,f177])).

fof(f6266,plain,
    ( ~ spl9_111
    | spl9_112
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1446,f1442,f175,f113,f108,f103,f98,f6263,f6259])).

fof(f6259,plain,
    ( spl9_111
  <=> r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).

fof(f1446,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_36 ),
    inference(superposition,[],[f221,f1444])).

fof(f221,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0))
        | ~ r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),X0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f220,f100])).

fof(f220,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0))
        | ~ r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),X0)
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f219,f115])).

fof(f219,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0))
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),X0)
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f218,f110])).

fof(f218,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),X0)
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f216,f105])).

fof(f216,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),X0)
        | v2_struct_0(sK0) )
    | ~ spl9_7 ),
    inference(superposition,[],[f81,f177])).

fof(f6108,plain,
    ( spl9_110
    | ~ spl9_17
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f1758,f409,f125,f113,f108,f103,f98,f416,f6106])).

fof(f409,plain,
    ( spl9_15
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f1758,plain,
    ( ! [X6,X5] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k2_lattices(sK0,X5,sK3(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X6)),X5) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f1757,f410])).

fof(f410,plain,
    ( v6_lattices(sK0)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f409])).

fof(f1757,plain,
    ( ! [X6,X5] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k2_lattices(sK0,X5,sK3(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X6)),X5)
        | ~ v6_lattices(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f1738,f100])).

fof(f1738,plain,
    ( ! [X6,X5] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | k2_lattices(sK0,X5,sK3(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X6)),X5)
        | ~ v6_lattices(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(resolution,[],[f1732,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
      | ~ v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(f5106,plain,
    ( spl9_109
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f4112,f2921,f125,f113,f108,f103,f98,f5103])).

fof(f5103,plain,
    ( spl9_109
  <=> r1_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_109])])).

fof(f4112,plain,
    ( r1_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_64 ),
    inference(superposition,[],[f4100,f2923])).

fof(f4100,plain,
    ( ! [X0] : r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f4090,f1732])).

fof(f4090,plain,
    ( ! [X0] :
        ( r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(resolution,[],[f4077,f2764])).

fof(f2764,plain,
    ( ! [X4,X3] :
        ( ~ r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2763,f100])).

fof(f2763,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | ~ r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2762,f1732])).

fof(f2762,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X4)),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2761,f115])).

fof(f2761,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X4)),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2760,f110])).

fof(f2760,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X4)),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2759,f105])).

fof(f2759,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X4)),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(duplicate_literal_removal,[],[f2752])).

fof(f2752,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X4)),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(resolution,[],[f2058,f96])).

fof(f2058,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0))))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),X1) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2057,f100])).

fof(f2057,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0))))
        | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),X1)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2056,f1732])).

fof(f2056,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0))))
        | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),X1)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f2050,f115])).

fof(f2050,plain,
    ( ! [X0,X1] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0))))
        | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),X1)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(resolution,[],[f2041,f83])).

fof(f4077,plain,
    ( ! [X0] : r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f4058,f1732])).

fof(f4058,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
        | r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(resolution,[],[f3902,f2041])).

fof(f3902,plain,
    ( ! [X10,X9] :
        ( ~ r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9))))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f3901,f100])).

fof(f3901,plain,
    ( ! [X10,X9] :
        ( r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9)))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9))))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f3900,f1732])).

fof(f3900,plain,
    ( ! [X10,X9] :
        ( r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9)))
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X9)),u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9))))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f3899,f115])).

fof(f3899,plain,
    ( ! [X10,X9] :
        ( r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9)))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X9)),u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9))))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f3898,f110])).

fof(f3898,plain,
    ( ! [X10,X9] :
        ( r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9)))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X9)),u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9))))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f3842,f105])).

fof(f3842,plain,
    ( ! [X10,X9] :
        ( r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9)))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X9)),u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9))))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(superposition,[],[f95,f1701])).

fof(f5076,plain,
    ( spl9_108
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f4097,f2921,f125,f113,f108,f103,f98,f5073])).

fof(f5073,plain,
    ( spl9_108
  <=> r3_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f4097,plain,
    ( r3_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_64 ),
    inference(superposition,[],[f4077,f2923])).

fof(f5065,plain,
    ( ~ spl9_106
    | spl9_107
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f5051,f1361,f1077,f211,f183,f113,f108,f103,f98,f5062,f5058])).

fof(f5058,plain,
    ( spl9_106
  <=> r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).

fof(f1361,plain,
    ( spl9_29
  <=> r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f5051,plain,
    ( r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0))
    | ~ r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f5038,f185])).

fof(f5038,plain,
    ( r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0))
    | ~ r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(superposition,[],[f3858,f213])).

fof(f3858,plain,
    ( ! [X1] :
        ( r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1))
        | ~ r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1)
        | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f3857,f100])).

fof(f3857,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f3856,f1079])).

fof(f3856,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f3855,f115])).

fof(f3855,plain,
    ( ! [X1] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f3854,f110])).

fof(f3854,plain,
    ( ! [X1] :
        ( ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f3847,f105])).

fof(f3847,plain,
    ( ! [X1] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(duplicate_literal_removal,[],[f3830])).

fof(f3830,plain,
    ( ! [X1] :
        ( ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1)
        | v2_struct_0(sK0)
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1))
        | ~ m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(resolution,[],[f95,f1602])).

fof(f1602,plain,
    ( ! [X2] :
        ( ~ r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1601,f100])).

fof(f1601,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | ~ r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1600,f1079])).

fof(f1600,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1599,f115])).

fof(f1599,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1598,f110])).

fof(f1598,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1597,f105])).

fof(f1597,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(duplicate_literal_removal,[],[f1596])).

fof(f1596,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2)
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(resolution,[],[f1368,f96])).

fof(f1368,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0) )
    | spl9_1
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1367,f100])).

fof(f1367,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1366,f1079])).

fof(f1366,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0)
        | v2_struct_0(sK0) )
    | ~ spl9_4
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f1365,f115])).

fof(f1365,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
        | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0)
        | v2_struct_0(sK0) )
    | ~ spl9_29 ),
    inference(resolution,[],[f1363,f83])).

fof(f1363,plain,
    ( r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f1361])).

fof(f4997,plain,
    ( spl9_105
    | ~ spl9_17
    | spl9_1
    | ~ spl9_15
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f1509,f1487,f409,f98,f416,f4995])).

fof(f4995,plain,
    ( spl9_105
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_105])])).

fof(f1509,plain,
    ( ! [X0] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),X0) )
    | spl9_1
    | ~ spl9_15
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f1508,f410])).

fof(f1508,plain,
    ( ! [X0] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),X0)
        | ~ v6_lattices(sK0) )
    | spl9_1
    | ~ spl9_37 ),
    inference(subsumption_resolution,[],[f1495,f100])).

fof(f1495,plain,
    ( ! [X0] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | k2_lattices(sK0,X0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),X0)
        | ~ v6_lattices(sK0) )
    | ~ spl9_37 ),
    inference(resolution,[],[f1489,f72])).

fof(f4924,plain,
    ( ~ spl9_17
    | spl9_104
    | spl9_1
    | spl9_6
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f1630,f1614,f125,f98,f4922,f416])).

fof(f4922,plain,
    ( spl9_104
  <=> ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,X2),sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).

fof(f1614,plain,
    ( spl9_41
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f1630,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,X2),sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,X2))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl9_1
    | spl9_6
    | ~ spl9_41 ),
    inference(subsumption_resolution,[],[f1629,f127])).

fof(f1629,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,X2),sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,X2))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_41 ),
    inference(subsumption_resolution,[],[f1624,f100])).

fof(f1624,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,X2),sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,X2))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | ~ spl9_41 ),
    inference(resolution,[],[f1615,f68])).

fof(f1615,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0) )
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f1614])).

fof(f4912,plain,
    ( ~ spl9_103
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_102 ),
    inference(avatar_split_clause,[],[f4903,f4892,f1487,f1442,f4909])).

fof(f4909,plain,
    ( spl9_103
  <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).

fof(f4903,plain,
    ( sK3(sK0,sK3(sK0,k5_lattices(sK0))) != k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_102 ),
    inference(subsumption_resolution,[],[f4898,f1489])).

fof(f4898,plain,
    ( sK3(sK0,sK3(sK0,k5_lattices(sK0))) != k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ spl9_36
    | ~ spl9_102 ),
    inference(superposition,[],[f4893,f1444])).

fof(f4894,plain,
    ( ~ spl9_17
    | spl9_102
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f3500,f409,f125,f113,f108,f103,f98,f4892,f416])).

fof(f3500,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0)))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f3499,f127])).

fof(f3499,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0)))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f3498,f100])).

fof(f3498,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0)))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_15 ),
    inference(duplicate_literal_removal,[],[f3495])).

fof(f3495,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0)))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0)))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_15 ),
    inference(superposition,[],[f67,f1775])).

fof(f1775,plain,
    ( ! [X15,X16] : k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X16)) = k2_lattices(sK0,k15_lattice3(sK0,X16),sK3(sK0,k15_lattice3(sK0,X15)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f1774,f115])).

fof(f1774,plain,
    ( ! [X15,X16] :
        ( k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X16)) = k2_lattices(sK0,k15_lattice3(sK0,X16),sK3(sK0,k15_lattice3(sK0,X15)))
        | ~ l3_lattices(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f1773,f410])).

fof(f1773,plain,
    ( ! [X15,X16] :
        ( k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X16)) = k2_lattices(sK0,k15_lattice3(sK0,X16),sK3(sK0,k15_lattice3(sK0,X15)))
        | ~ v6_lattices(sK0)
        | ~ l3_lattices(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f1747,f100])).

fof(f1747,plain,
    ( ! [X15,X16] :
        ( v2_struct_0(sK0)
        | k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X16)) = k2_lattices(sK0,k15_lattice3(sK0,X16),sK3(sK0,k15_lattice3(sK0,X15)))
        | ~ v6_lattices(sK0)
        | ~ l3_lattices(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(resolution,[],[f1732,f380])).

fof(f380,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X2))
      | v2_struct_0(X2)
      | k2_lattices(X2,X3,k15_lattice3(X2,X4)) = k2_lattices(X2,k15_lattice3(X2,X4),X3)
      | ~ v6_lattices(X2)
      | ~ l3_lattices(X2) ) ),
    inference(subsumption_resolution,[],[f378,f50])).

fof(f378,plain,(
    ! [X4,X2,X3] :
      ( ~ l1_lattices(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v2_struct_0(X2)
      | k2_lattices(X2,X3,k15_lattice3(X2,X4)) = k2_lattices(X2,k15_lattice3(X2,X4),X3)
      | ~ v6_lattices(X2)
      | ~ l3_lattices(X2) ) ),
    inference(duplicate_literal_removal,[],[f364])).

fof(f364,plain,(
    ! [X4,X2,X3] :
      ( ~ l1_lattices(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | v2_struct_0(X2)
      | k2_lattices(X2,X3,k15_lattice3(X2,X4)) = k2_lattices(X2,k15_lattice3(X2,X4),X3)
      | ~ v6_lattices(X2)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f72,f87])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_lattices(X0,sK3(X0,X1),X1) != X1
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k2_lattices(X0,X1,sK3(X0,X1)) != X1
      | v2_struct_0(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4829,plain,
    ( ~ spl9_17
    | spl9_101
    | spl9_1
    | spl9_6
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f1383,f700,f125,f98,f4827,f416])).

fof(f4827,plain,
    ( spl9_101
  <=> ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,sK3(sK0,X2)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_101])])).

fof(f700,plain,
    ( spl9_19
  <=> ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,X2),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f1383,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,sK3(sK0,X2)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,X2)))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl9_1
    | spl9_6
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f1382,f127])).

fof(f1382,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,sK3(sK0,X2)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,X2)))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f1375,f100])).

fof(f1375,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,sK3(sK0,X2)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,X2)))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | ~ spl9_19 ),
    inference(resolution,[],[f701,f68])).

fof(f701,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,sK3(sK0,X2),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,X2)) )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f700])).

fof(f4409,plain,
    ( ~ spl9_68
    | ~ spl9_69
    | spl9_100
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f4384,f113,f108,f103,f98,f4407,f3350,f3346])).

fof(f4407,plain,
    ( spl9_100
  <=> ! [X0] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f4384,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f4383,f100])).

fof(f4383,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f4382,f115])).

fof(f4382,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f4374])).

fof(f4374,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(resolution,[],[f4369,f59])).

fof(f4259,plain,
    ( spl9_99
    | ~ spl9_24
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f4247,f4242,f1036,f4256])).

fof(f4256,plain,
    ( spl9_99
  <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).

fof(f1036,plain,
    ( spl9_24
  <=> sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f4247,plain,
    ( sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_24
    | ~ spl9_98 ),
    inference(superposition,[],[f4243,f1038])).

fof(f1038,plain,
    ( sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f1036])).

fof(f4244,plain,
    ( spl9_98
    | ~ spl9_68
    | ~ spl9_69
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(avatar_split_clause,[],[f4117,f125,f113,f108,f103,f98,f3350,f3346,f4242])).

fof(f4117,plain,
    ( ! [X0] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f4116,f100])).

fof(f4116,plain,
    ( ! [X0] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f4115,f1732])).

fof(f4115,plain,
    ( ! [X0] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
        | sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(subsumption_resolution,[],[f4114,f115])).

fof(f4114,plain,
    ( ! [X0] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
        | sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(duplicate_literal_removal,[],[f4106])).

fof(f4106,plain,
    ( ! [X0] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))
        | sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))
        | v2_struct_0(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6 ),
    inference(resolution,[],[f4100,f59])).

fof(f4227,plain,
    ( spl9_97
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_93 ),
    inference(avatar_split_clause,[],[f4129,f4119,f1487,f113,f108,f103,f98,f4224])).

fof(f4224,plain,
    ( spl9_97
  <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).

fof(f4119,plain,
    ( spl9_93
  <=> r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).

fof(f4129,plain,
    ( sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_93 ),
    inference(subsumption_resolution,[],[f4128,f100])).

fof(f4128,plain,
    ( v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_93 ),
    inference(subsumption_resolution,[],[f4127,f105])).

fof(f4127,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_93 ),
    inference(subsumption_resolution,[],[f4126,f1489])).

fof(f4126,plain,
    ( ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_93 ),
    inference(subsumption_resolution,[],[f4125,f115])).

fof(f4125,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_3
    | ~ spl9_93 ),
    inference(subsumption_resolution,[],[f4124,f110])).

fof(f4124,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_93 ),
    inference(duplicate_literal_removal,[],[f4123])).

fof(f4123,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_93 ),
    inference(resolution,[],[f4121,f596])).

fof(f596,plain,(
    ! [X2,X3,X1] :
      ( ~ r3_lattices(X1,X2,X3)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | sK8(X3,X1,X2) = X3 ) ),
    inference(duplicate_literal_removal,[],[f595])).

fof(f595,plain,(
    ! [X2,X3,X1] :
      ( ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r3_lattices(X1,X2,X3)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sK8(X3,X1,X2) = X3
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f96,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sK8(X0,X1,X2) = X0
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4121,plain,
    ( r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_93 ),
    inference(avatar_component_clause,[],[f4119])).

fof(f4191,plain,
    ( spl9_96
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f4110,f1442,f125,f113,f108,f103,f98,f4188])).

fof(f4188,plain,
    ( spl9_96
  <=> r1_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f4110,plain,
    ( r1_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(superposition,[],[f4100,f1444])).

fof(f4179,plain,
    ( spl9_95
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f4095,f1442,f125,f113,f108,f103,f98,f4176])).

fof(f4176,plain,
    ( spl9_95
  <=> r3_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).

fof(f4095,plain,
    ( r3_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(superposition,[],[f4077,f1444])).

fof(f4134,plain,
    ( spl9_94
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f4109,f1036,f125,f113,f108,f103,f98,f4131])).

fof(f4131,plain,
    ( spl9_94
  <=> r1_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f4109,plain,
    ( r1_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_24 ),
    inference(superposition,[],[f4100,f1038])).

fof(f4122,plain,
    ( spl9_93
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f4094,f1036,f125,f113,f108,f103,f98,f4119])).

fof(f4094,plain,
    ( r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_24 ),
    inference(superposition,[],[f4077,f1038])).

fof(f4053,plain,
    ( ~ spl9_91
    | spl9_92
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f3976,f1334,f1077,f335,f183,f113,f108,f103,f98,f4050,f4046])).

fof(f4046,plain,
    ( spl9_91
  <=> r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f4050,plain,
    ( spl9_92
  <=> r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).

fof(f1334,plain,
    ( spl9_28
  <=> sK3(sK0,k5_lattices(sK0)) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f3976,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3967,f1079])).

fof(f3967,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_28 ),
    inference(superposition,[],[f3853,f1336])).

fof(f1336,plain,
    ( sK3(sK0,k5_lattices(sK0)) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f1334])).

fof(f4041,plain,
    ( spl9_90
    | ~ spl9_68
    | ~ spl9_69
    | spl9_1
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f4029,f4021,f1077,f113,f98,f3350,f3346,f4038])).

fof(f4038,plain,
    ( spl9_90
  <=> sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f4021,plain,
    ( spl9_88
  <=> r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f4029,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_88 ),
    inference(subsumption_resolution,[],[f4028,f100])).

fof(f4028,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_88 ),
    inference(subsumption_resolution,[],[f4027,f1079])).

fof(f4027,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_88 ),
    inference(subsumption_resolution,[],[f4026,f115])).

fof(f4026,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_88 ),
    inference(duplicate_literal_removal,[],[f4025])).

fof(f4025,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_88 ),
    inference(resolution,[],[f4023,f59])).

fof(f4023,plain,
    ( r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f4021])).

fof(f4034,plain,
    ( spl9_89
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_87 ),
    inference(avatar_split_clause,[],[f4019,f4007,f1077,f113,f108,f103,f98,f4031])).

fof(f4031,plain,
    ( spl9_89
  <=> sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).

fof(f4007,plain,
    ( spl9_87
  <=> r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).

fof(f4019,plain,
    ( sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_87 ),
    inference(subsumption_resolution,[],[f4018,f100])).

fof(f4018,plain,
    ( v2_struct_0(sK0)
    | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_87 ),
    inference(subsumption_resolution,[],[f4017,f105])).

fof(f4017,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_87 ),
    inference(subsumption_resolution,[],[f4016,f1079])).

fof(f4016,plain,
    ( ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_87 ),
    inference(subsumption_resolution,[],[f4015,f115])).

fof(f4015,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_3
    | ~ spl9_87 ),
    inference(subsumption_resolution,[],[f4013,f110])).

fof(f4013,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_87 ),
    inference(duplicate_literal_removal,[],[f4012])).

fof(f4012,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_87 ),
    inference(resolution,[],[f4009,f596])).

fof(f4009,plain,
    ( r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_87 ),
    inference(avatar_component_clause,[],[f4007])).

fof(f4024,plain,
    ( spl9_88
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29
    | ~ spl9_87 ),
    inference(avatar_split_clause,[],[f4014,f4007,f1361,f1077,f113,f108,f103,f98,f4021])).

fof(f4014,plain,
    ( r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29
    | ~ spl9_87 ),
    inference(subsumption_resolution,[],[f4011,f1079])).

fof(f4011,plain,
    ( r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_29
    | ~ spl9_87 ),
    inference(resolution,[],[f4009,f1602])).

fof(f4010,plain,
    ( spl9_87
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f4000,f1334,f1077,f113,f108,f103,f98,f4007])).

fof(f4000,plain,
    ( r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f3999,f1336])).

fof(f3999,plain,
    ( r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3998,f1079])).

fof(f3998,plain,
    ( ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(forward_demodulation,[],[f3997,f1336])).

fof(f3997,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3996,f100])).

fof(f3996,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3995,f115])).

fof(f3995,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3994,f110])).

fof(f3994,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3992,f105])).

fof(f3992,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(duplicate_literal_removal,[],[f3982])).

fof(f3982,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(resolution,[],[f3882,f94])).

fof(f3882,plain,
    ( ! [X4] :
        ( ~ r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3881,f100])).

fof(f3881,plain,
    ( ! [X4] :
        ( r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3880,f1079])).

fof(f3880,plain,
    ( ! [X4] :
        ( r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0)))
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3879,f115])).

fof(f3879,plain,
    ( ! [X4] :
        ( r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0)))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3878,f110])).

fof(f3878,plain,
    ( ! [X4] :
        ( r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0)))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f3838,f105])).

fof(f3838,plain,
    ( ! [X4] :
        ( r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0)))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl9_28 ),
    inference(superposition,[],[f95,f1336])).

fof(f3959,plain,
    ( spl9_86
    | ~ spl9_68
    | ~ spl9_69
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f3947,f3939,f183,f113,f98,f3350,f3346,f3956])).

fof(f3956,plain,
    ( spl9_86
  <=> k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f3939,plain,
    ( spl9_84
  <=> r1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f3947,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f3946,f100])).

fof(f3946,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f3945,f185])).

fof(f3945,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f3944,f115])).

fof(f3944,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_84 ),
    inference(duplicate_literal_removal,[],[f3943])).

fof(f3943,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_84 ),
    inference(resolution,[],[f3941,f59])).

fof(f3941,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ spl9_84 ),
    inference(avatar_component_clause,[],[f3939])).

fof(f3952,plain,
    ( spl9_85
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f3937,f346,f183,f113,f108,f103,f98,f3949])).

fof(f3949,plain,
    ( spl9_85
  <=> k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).

fof(f346,plain,
    ( spl9_13
  <=> r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f3937,plain,
    ( k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f3936,f100])).

fof(f3936,plain,
    ( v2_struct_0(sK0)
    | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f3935,f105])).

fof(f3935,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f3934,f185])).

fof(f3934,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f3933,f115])).

fof(f3933,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0))
    | ~ spl9_3
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f3931,f110])).

fof(f3931,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0))
    | ~ spl9_13 ),
    inference(duplicate_literal_removal,[],[f3930])).

fof(f3930,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0))
    | ~ spl9_13 ),
    inference(resolution,[],[f348,f596])).

fof(f348,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f346])).

fof(f3942,plain,
    ( spl9_84
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f3932,f346,f335,f183,f113,f108,f103,f98,f3939])).

fof(f3932,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f3929,f185])).

fof(f3929,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | r1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_11
    | ~ spl9_13 ),
    inference(resolution,[],[f348,f602])).

fof(f3928,plain,
    ( spl9_13
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f3922,f211,f183,f113,f108,f103,f98,f346])).

fof(f3922,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f3921,f213])).

fof(f3921,plain,
    ( r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f3920,f185])).

fof(f3920,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(forward_demodulation,[],[f3919,f213])).

fof(f3919,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f3918,f100])).

fof(f3918,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f3917,f115])).

fof(f3917,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f3916,f110])).

fof(f3916,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f3914,f105])).

fof(f3914,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(duplicate_literal_removal,[],[f3904])).

fof(f3904,plain,
    ( ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0))
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(resolution,[],[f3873,f94])).

fof(f3873,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r3_lattices(sK0,X0,k5_lattices(sK0)) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f3872,f100])).

fof(f3872,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,X0,k5_lattices(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f3871,f185])).

fof(f3871,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,X0,k5_lattices(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f3870,f115])).

fof(f3870,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,X0,k5_lattices(sK0))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f3869,f110])).

fof(f3869,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,X0,k5_lattices(sK0))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f3835,f105])).

fof(f3835,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,X0,k5_lattices(sK0))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(superposition,[],[f95,f213])).

fof(f3722,plain,
    ( spl9_83
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f2973,f2921,f125,f113,f108,f103,f98,f3719])).

fof(f3719,plain,
    ( spl9_83
  <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).

fof(f2973,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_64 ),
    inference(superposition,[],[f1995,f2923])).

fof(f3707,plain,
    ( spl9_82
    | ~ spl9_62
    | ~ spl9_68
    | ~ spl9_69
    | spl9_1
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f3566,f3559,f1077,f113,f98,f3350,f3346,f2784,f3704])).

fof(f3704,plain,
    ( spl9_82
  <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f3559,plain,
    ( spl9_74
  <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f3566,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_74 ),
    inference(subsumption_resolution,[],[f3565,f100])).

fof(f3565,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_74 ),
    inference(subsumption_resolution,[],[f3564,f1079])).

fof(f3564,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_74 ),
    inference(subsumption_resolution,[],[f3563,f115])).

fof(f3563,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_74 ),
    inference(resolution,[],[f3561,f59])).

fof(f3561,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_74 ),
    inference(avatar_component_clause,[],[f3559])).

fof(f3696,plain,
    ( spl9_81
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f2979,f2921,f113,f108,f103,f98,f3693])).

fof(f3693,plain,
    ( spl9_81
  <=> sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = sK8(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK0,k15_lattice3(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f2979,plain,
    ( sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = sK8(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK0,k15_lattice3(sK0,k1_xboole_0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_64 ),
    inference(superposition,[],[f2657,f2923])).

fof(f2657,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = sK8(k15_lattice3(sK0,X0),sK0,k15_lattice3(sK0,k1_xboole_0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f2656,f115])).

fof(f2656,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) = sK8(k15_lattice3(sK0,X0),sK0,k15_lattice3(sK0,k1_xboole_0))
        | ~ l3_lattices(sK0) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f2655,f100])).

fof(f2655,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | k15_lattice3(sK0,X0) = sK8(k15_lattice3(sK0,X0),sK0,k15_lattice3(sK0,k1_xboole_0))
        | ~ l3_lattices(sK0) )
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f2654,f105])).

fof(f2654,plain,
    ( ! [X0] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | k15_lattice3(sK0,X0) = sK8(k15_lattice3(sK0,X0),sK0,k15_lattice3(sK0,k1_xboole_0))
        | ~ l3_lattices(sK0) )
    | ~ spl9_3 ),
    inference(resolution,[],[f2653,f110])).

fof(f2653,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | k15_lattice3(X0,X1) = sK8(k15_lattice3(X0,X1),X0,k15_lattice3(X0,k1_xboole_0))
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f2585,f49])).

fof(f2585,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | k15_lattice3(X2,X4) = sK8(k15_lattice3(X2,X4),X2,k15_lattice3(X2,X3))
      | ~ v4_lattice3(X2) ) ),
    inference(subsumption_resolution,[],[f2584,f87])).

fof(f2584,plain,(
    ! [X4,X2,X3] :
      ( ~ v4_lattice3(X2)
      | ~ l3_lattices(X2)
      | ~ m1_subset_1(k15_lattice3(X2,X4),u1_struct_0(X2))
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | k15_lattice3(X2,X4) = sK8(k15_lattice3(X2,X4),X2,k15_lattice3(X2,X3))
      | ~ r1_tarski(X3,X4) ) ),
    inference(subsumption_resolution,[],[f2573,f87])).

fof(f2573,plain,(
    ! [X4,X2,X3] :
      ( ~ v4_lattice3(X2)
      | ~ l3_lattices(X2)
      | ~ m1_subset_1(k15_lattice3(X2,X3),u1_struct_0(X2))
      | ~ m1_subset_1(k15_lattice3(X2,X4),u1_struct_0(X2))
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | k15_lattice3(X2,X4) = sK8(k15_lattice3(X2,X4),X2,k15_lattice3(X2,X3))
      | ~ r1_tarski(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f2552])).

fof(f2552,plain,(
    ! [X4,X2,X3] :
      ( ~ v4_lattice3(X2)
      | ~ l3_lattices(X2)
      | ~ m1_subset_1(k15_lattice3(X2,X3),u1_struct_0(X2))
      | ~ m1_subset_1(k15_lattice3(X2,X4),u1_struct_0(X2))
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | k15_lattice3(X2,X4) = sK8(k15_lattice3(X2,X4),X2,k15_lattice3(X2,X3))
      | ~ v10_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ l3_lattices(X2)
      | ~ r1_tarski(X3,X4)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f596,f81])).

fof(f3691,plain,
    ( ~ spl9_17
    | ~ spl9_80
    | spl9_1
    | spl9_6
    | ~ spl9_25
    | ~ spl9_79 ),
    inference(avatar_split_clause,[],[f3682,f3673,f1077,f125,f98,f3688,f416])).

fof(f3688,plain,
    ( spl9_80
  <=> sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f3673,plain,
    ( spl9_79
  <=> k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).

fof(f3682,plain,
    ( sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ l1_lattices(sK0)
    | spl9_1
    | spl9_6
    | ~ spl9_25
    | ~ spl9_79 ),
    inference(subsumption_resolution,[],[f3681,f127])).

fof(f3681,plain,
    ( sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ l1_lattices(sK0)
    | v13_lattices(sK0)
    | spl9_1
    | ~ spl9_25
    | ~ spl9_79 ),
    inference(subsumption_resolution,[],[f3680,f100])).

fof(f3680,plain,
    ( sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl9_25
    | ~ spl9_79 ),
    inference(subsumption_resolution,[],[f3679,f1079])).

fof(f3679,plain,
    ( sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl9_79 ),
    inference(duplicate_literal_removal,[],[f3677])).

fof(f3677,plain,
    ( sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl9_79 ),
    inference(superposition,[],[f67,f3675])).

fof(f3675,plain,
    ( k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_79 ),
    inference(avatar_component_clause,[],[f3673])).

fof(f3676,plain,
    ( spl9_79
    | ~ spl9_37
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f1619,f1614,f1487,f3673])).

fof(f1619,plain,
    ( k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_37
    | ~ spl9_41 ),
    inference(resolution,[],[f1615,f1489])).

fof(f3666,plain,
    ( spl9_78
    | ~ spl9_16
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f1832,f1826,f413,f3663])).

fof(f3663,plain,
    ( spl9_78
  <=> k2_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).

fof(f413,plain,
    ( spl9_16
  <=> ! [X21] :
        ( ~ m1_subset_1(X21,u1_struct_0(sK0))
        | k2_lattices(sK0,X21,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X21) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f1832,plain,
    ( k2_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ spl9_16
    | ~ spl9_42 ),
    inference(resolution,[],[f1828,f414])).

fof(f414,plain,
    ( ! [X21] :
        ( ~ m1_subset_1(X21,u1_struct_0(sK0))
        | k2_lattices(sK0,X21,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X21) )
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f413])).

fof(f3596,plain,
    ( ~ spl9_62
    | spl9_77
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_75 ),
    inference(avatar_split_clause,[],[f3588,f3568,f1487,f113,f108,f103,f98,f3593,f2784])).

fof(f3568,plain,
    ( spl9_75
  <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_75])])).

fof(f3588,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_75 ),
    inference(subsumption_resolution,[],[f3586,f1489])).

fof(f3586,plain,
    ( ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_75 ),
    inference(resolution,[],[f3570,f3280])).

fof(f3570,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_75 ),
    inference(avatar_component_clause,[],[f3568])).

fof(f3585,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_36
    | spl9_75 ),
    inference(avatar_contradiction_clause,[],[f3584])).

fof(f3584,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_36
    | spl9_75 ),
    inference(subsumption_resolution,[],[f3583,f49])).

fof(f3583,plain,
    ( ~ r1_tarski(k1_xboole_0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_36
    | spl9_75 ),
    inference(resolution,[],[f3569,f1451])).

fof(f1451,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
        | ~ r1_tarski(X0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_36 ),
    inference(superposition,[],[f264,f1444])).

fof(f3569,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_75 ),
    inference(avatar_component_clause,[],[f3568])).

fof(f3582,plain,
    ( ~ spl9_75
    | ~ spl9_62
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | spl9_76 ),
    inference(avatar_split_clause,[],[f3581,f3572,f1487,f113,f108,f103,f98,f2784,f3568])).

fof(f3572,plain,
    ( spl9_76
  <=> r2_hidden(sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f3581,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | spl9_76 ),
    inference(subsumption_resolution,[],[f3580,f100])).

fof(f3580,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | spl9_76 ),
    inference(subsumption_resolution,[],[f3579,f1489])).

fof(f3579,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_76 ),
    inference(subsumption_resolution,[],[f3578,f115])).

fof(f3578,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | spl9_76 ),
    inference(subsumption_resolution,[],[f3577,f110])).

fof(f3577,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | spl9_76 ),
    inference(subsumption_resolution,[],[f3576,f105])).

fof(f3576,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | v2_struct_0(sK0)
    | spl9_76 ),
    inference(resolution,[],[f3574,f96])).

fof(f3574,plain,
    ( ~ r2_hidden(sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | spl9_76 ),
    inference(avatar_component_clause,[],[f3572])).

fof(f3575,plain,
    ( spl9_75
    | ~ spl9_76
    | ~ spl9_36
    | ~ spl9_71 ),
    inference(avatar_split_clause,[],[f3529,f3522,f1442,f3572,f3568])).

fof(f3529,plain,
    ( ~ r2_hidden(sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_36
    | ~ spl9_71 ),
    inference(superposition,[],[f3523,f1444])).

fof(f3562,plain,
    ( ~ spl9_62
    | spl9_74
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_72 ),
    inference(avatar_split_clause,[],[f3554,f3534,f1077,f113,f108,f103,f98,f3559,f2784])).

fof(f3534,plain,
    ( spl9_72
  <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f3554,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | ~ spl9_72 ),
    inference(subsumption_resolution,[],[f3552,f1079])).

fof(f3552,plain,
    ( ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_72 ),
    inference(resolution,[],[f3536,f3280])).

fof(f3536,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f3534])).

fof(f3551,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24
    | spl9_72 ),
    inference(avatar_contradiction_clause,[],[f3550])).

fof(f3550,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24
    | spl9_72 ),
    inference(subsumption_resolution,[],[f3549,f49])).

fof(f3549,plain,
    ( ~ r1_tarski(k1_xboole_0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24
    | spl9_72 ),
    inference(resolution,[],[f3535,f1296])).

fof(f1296,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k5_lattices(sK0)))
        | ~ r1_tarski(X0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(superposition,[],[f264,f1038])).

fof(f3535,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | spl9_72 ),
    inference(avatar_component_clause,[],[f3534])).

fof(f3548,plain,
    ( ~ spl9_72
    | ~ spl9_62
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | spl9_73 ),
    inference(avatar_split_clause,[],[f3547,f3538,f1077,f113,f108,f103,f98,f2784,f3534])).

fof(f3538,plain,
    ( spl9_73
  <=> r2_hidden(sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).

fof(f3547,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | spl9_73 ),
    inference(subsumption_resolution,[],[f3546,f100])).

fof(f3546,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25
    | spl9_73 ),
    inference(subsumption_resolution,[],[f3545,f1079])).

fof(f3545,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_73 ),
    inference(subsumption_resolution,[],[f3544,f115])).

fof(f3544,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | spl9_73 ),
    inference(subsumption_resolution,[],[f3543,f110])).

fof(f3543,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | spl9_73 ),
    inference(subsumption_resolution,[],[f3542,f105])).

fof(f3542,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | spl9_73 ),
    inference(resolution,[],[f3540,f96])).

fof(f3540,plain,
    ( ~ r2_hidden(sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | spl9_73 ),
    inference(avatar_component_clause,[],[f3538])).

fof(f3541,plain,
    ( spl9_72
    | ~ spl9_73
    | ~ spl9_24
    | ~ spl9_71 ),
    inference(avatar_split_clause,[],[f3528,f3522,f1036,f3538,f3534])).

fof(f3528,plain,
    ( ~ r2_hidden(sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_24
    | ~ spl9_71 ),
    inference(superposition,[],[f3523,f1038])).

fof(f3524,plain,
    ( ~ spl9_62
    | spl9_71
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f2669,f113,f108,f103,f98,f3522,f2784])).

fof(f2669,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f2668,f100])).

fof(f2668,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f2667,f115])).

fof(f2667,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f2666,f110])).

fof(f2666,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f2664,f105])).

fof(f2664,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(superposition,[],[f90,f2657])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X1,X2,sK8(X0,X1,X2))
      | ~ v10_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3367,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_69 ),
    inference(avatar_contradiction_clause,[],[f3366])).

fof(f3366,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_69 ),
    inference(subsumption_resolution,[],[f3365,f115])).

fof(f3365,plain,
    ( ~ l3_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | spl9_69 ),
    inference(subsumption_resolution,[],[f3364,f105])).

fof(f3364,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_1
    | spl9_69 ),
    inference(subsumption_resolution,[],[f3363,f100])).

fof(f3363,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_69 ),
    inference(resolution,[],[f3352,f56])).

fof(f3352,plain,
    ( ~ v8_lattices(sK0)
    | spl9_69 ),
    inference(avatar_component_clause,[],[f3350])).

fof(f3362,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_68 ),
    inference(avatar_contradiction_clause,[],[f3361])).

fof(f3361,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_68 ),
    inference(subsumption_resolution,[],[f3360,f115])).

fof(f3360,plain,
    ( ~ l3_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | spl9_68 ),
    inference(subsumption_resolution,[],[f3359,f105])).

fof(f3359,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_1
    | spl9_68 ),
    inference(subsumption_resolution,[],[f3358,f100])).

fof(f3358,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_68 ),
    inference(resolution,[],[f3348,f57])).

fof(f3348,plain,
    ( ~ v9_lattices(sK0)
    | spl9_68 ),
    inference(avatar_component_clause,[],[f3346])).

fof(f3357,plain,
    ( ~ spl9_62
    | ~ spl9_68
    | ~ spl9_69
    | spl9_70
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_67 ),
    inference(avatar_split_clause,[],[f3294,f3286,f183,f113,f103,f98,f3354,f3350,f3346,f2784])).

fof(f3354,plain,
    ( spl9_70
  <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f3286,plain,
    ( spl9_67
  <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f3294,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,k1_xboole_0))
    | ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_67 ),
    inference(forward_demodulation,[],[f3293,f406])).

fof(f406,plain,
    ( ! [X0] : k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f405,f115])).

fof(f405,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK0)
        | k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) )
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f404,f100])).

fof(f404,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) )
    | ~ spl9_2 ),
    inference(resolution,[],[f403,f105])).

fof(f403,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k2_lattices(X0,k5_lattices(X0),k15_lattice3(X0,X1)) = k2_lattices(X0,k15_lattice3(X0,X1),k5_lattices(X0)) ) ),
    inference(duplicate_literal_removal,[],[f402])).

fof(f402,plain,(
    ! [X0,X1] :
      ( k2_lattices(X0,k5_lattices(X0),k15_lattice3(X0,X1)) = k2_lattices(X0,k15_lattice3(X0,X1),k5_lattices(X0))
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f400,f54])).

fof(f54,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f400,plain,(
    ! [X2,X1] :
      ( ~ v6_lattices(X1)
      | k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1)) = k2_lattices(X1,k5_lattices(X1),k15_lattice3(X1,X2))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f398,f50])).

fof(f398,plain,(
    ! [X2,X1] :
      ( ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1)) = k2_lattices(X1,k5_lattices(X1),k15_lattice3(X1,X2))
      | ~ v6_lattices(X1)
      | ~ l3_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f384])).

fof(f384,plain,(
    ! [X2,X1] :
      ( ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1)) = k2_lattices(X1,k5_lattices(X1),k15_lattice3(X1,X2))
      | ~ v6_lattices(X1)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f379,f87])).

fof(f379,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | k2_lattices(X0,X1,k5_lattices(X0)) = k2_lattices(X0,k5_lattices(X0),X1)
      | ~ v6_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f363])).

fof(f363,plain,(
    ! [X0,X1] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | k2_lattices(X0,X1,k5_lattices(X0)) = k2_lattices(X0,k5_lattices(X0),X1)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f72,f60])).

fof(f3293,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_67 ),
    inference(subsumption_resolution,[],[f3292,f100])).

fof(f3292,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_67 ),
    inference(subsumption_resolution,[],[f3291,f185])).

fof(f3291,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_67 ),
    inference(subsumption_resolution,[],[f3290,f115])).

fof(f3290,plain,
    ( ~ v8_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_67 ),
    inference(resolution,[],[f3288,f59])).

fof(f3288,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl9_67 ),
    inference(avatar_component_clause,[],[f3286])).

fof(f3289,plain,
    ( spl9_67
    | ~ spl9_62
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_61 ),
    inference(avatar_split_clause,[],[f3281,f2780,f183,f113,f108,f103,f98,f2784,f3286])).

fof(f2780,plain,
    ( spl9_61
  <=> r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f3281,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_61 ),
    inference(subsumption_resolution,[],[f3268,f185])).

fof(f3268,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_61 ),
    inference(resolution,[],[f3088,f2781])).

fof(f2781,plain,
    ( r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ spl9_61 ),
    inference(avatar_component_clause,[],[f2780])).

fof(f3032,plain,
    ( spl9_66
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f2054,f1442,f125,f113,f108,f103,f98,f3029])).

fof(f3029,plain,
    ( spl9_66
  <=> r3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f2054,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(superposition,[],[f2041,f1444])).

fof(f2999,plain,
    ( spl9_65
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f1858,f1826,f113,f108,f103,f98,f2996])).

fof(f2996,plain,
    ( spl9_65
  <=> sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f1858,plain,
    ( sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f1857,f100])).

fof(f1857,plain,
    ( v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f1856,f115])).

fof(f1856,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f1855,f110])).

fof(f1855,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | ~ spl9_2
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f1837,f105])).

fof(f1837,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | ~ spl9_42 ),
    inference(resolution,[],[f1828,f75])).

fof(f2924,plain,
    ( spl9_64
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f1854,f1826,f113,f108,f103,f98,f2921])).

fof(f1854,plain,
    ( sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f1853,f100])).

fof(f1853,plain,
    ( v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f1852,f115])).

fof(f1852,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f1851,f110])).

fof(f1851,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | ~ spl9_2
    | ~ spl9_42 ),
    inference(subsumption_resolution,[],[f1836,f105])).

fof(f1836,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))
    | ~ spl9_42 ),
    inference(resolution,[],[f1828,f74])).

fof(f2805,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | spl9_63 ),
    inference(avatar_contradiction_clause,[],[f2804])).

fof(f2804,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | spl9_63 ),
    inference(subsumption_resolution,[],[f2803,f49])).

fof(f2803,plain,
    ( ~ r1_tarski(k1_xboole_0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | spl9_63 ),
    inference(resolution,[],[f2789,f225])).

fof(f2789,plain,
    ( ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl9_63 ),
    inference(avatar_component_clause,[],[f2788])).

fof(f2788,plain,
    ( spl9_63
  <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).

fof(f2802,plain,
    ( spl9_1
    | ~ spl9_4
    | spl9_62 ),
    inference(avatar_contradiction_clause,[],[f2801])).

fof(f2801,plain,
    ( $false
    | spl9_1
    | ~ spl9_4
    | spl9_62 ),
    inference(subsumption_resolution,[],[f2800,f100])).

fof(f2800,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_4
    | spl9_62 ),
    inference(subsumption_resolution,[],[f2799,f115])).

fof(f2799,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl9_62 ),
    inference(resolution,[],[f2786,f87])).

fof(f2786,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl9_62 ),
    inference(avatar_component_clause,[],[f2784])).

fof(f2798,plain,
    ( ~ spl9_63
    | ~ spl9_62
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | spl9_61 ),
    inference(avatar_split_clause,[],[f2797,f2780,f183,f113,f108,f103,f98,f2784,f2788])).

fof(f2797,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | spl9_61 ),
    inference(subsumption_resolution,[],[f2796,f100])).

fof(f2796,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | spl9_61 ),
    inference(subsumption_resolution,[],[f2795,f185])).

fof(f2795,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_61 ),
    inference(subsumption_resolution,[],[f2794,f115])).

fof(f2794,plain,
    ( ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | spl9_61 ),
    inference(subsumption_resolution,[],[f2793,f110])).

fof(f2793,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | spl9_61 ),
    inference(subsumption_resolution,[],[f2792,f105])).

fof(f2792,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | v2_struct_0(sK0)
    | spl9_61 ),
    inference(resolution,[],[f2782,f96])).

fof(f2782,plain,
    ( ~ r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | spl9_61 ),
    inference(avatar_component_clause,[],[f2780])).

fof(f2791,plain,
    ( ~ spl9_61
    | ~ spl9_62
    | spl9_63
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f2680,f2671,f113,f108,f103,f98,f2788,f2784,f2780])).

fof(f2671,plain,
    ( spl9_58
  <=> k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k15_lattice3(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f2680,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_58 ),
    inference(subsumption_resolution,[],[f2679,f100])).

fof(f2679,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_58 ),
    inference(subsumption_resolution,[],[f2678,f115])).

fof(f2678,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_58 ),
    inference(subsumption_resolution,[],[f2677,f110])).

fof(f2677,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ spl9_2
    | ~ spl9_58 ),
    inference(subsumption_resolution,[],[f2675,f105])).

fof(f2675,plain,
    ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))
    | ~ spl9_58 ),
    inference(superposition,[],[f90,f2673])).

fof(f2673,plain,
    ( k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k15_lattice3(sK0,k1_xboole_0))
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f2671])).

fof(f2708,plain,
    ( spl9_60
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f2661,f1442,f113,f108,f103,f98,f2705])).

fof(f2705,plain,
    ( spl9_60
  <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,k15_lattice3(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f2661,plain,
    ( sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,k15_lattice3(sK0,k1_xboole_0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_36 ),
    inference(superposition,[],[f2657,f1444])).

fof(f2685,plain,
    ( spl9_59
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f2660,f1036,f113,f108,f103,f98,f2682])).

fof(f2682,plain,
    ( spl9_59
  <=> sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,k15_lattice3(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f2660,plain,
    ( sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,k15_lattice3(sK0,k1_xboole_0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(superposition,[],[f2657,f1038])).

fof(f2674,plain,
    ( spl9_58
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f2658,f175,f113,f108,f103,f98,f2671])).

fof(f2658,plain,
    ( k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k15_lattice3(sK0,k1_xboole_0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(superposition,[],[f2657,f177])).

fof(f2549,plain,
    ( ~ spl9_17
    | ~ spl9_57
    | spl9_1
    | spl9_6
    | ~ spl9_8
    | ~ spl9_21 ),
    inference(avatar_split_clause,[],[f2544,f837,f183,f125,f98,f2546,f416])).

fof(f2544,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ l1_lattices(sK0)
    | spl9_1
    | spl9_6
    | ~ spl9_8
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f2543,f127])).

fof(f2543,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ l1_lattices(sK0)
    | v13_lattices(sK0)
    | spl9_1
    | ~ spl9_8
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f2542,f100])).

fof(f2542,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl9_8
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f2541,f185])).

fof(f2541,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl9_21 ),
    inference(duplicate_literal_removal,[],[f2540])).

fof(f2540,plain,
    ( k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | v13_lattices(sK0)
    | ~ spl9_21 ),
    inference(superposition,[],[f67,f839])).

fof(f2445,plain,
    ( spl9_56
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f2130,f1442,f125,f113,f108,f103,f98,f2442])).

fof(f2442,plain,
    ( spl9_56
  <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f2130,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(superposition,[],[f1995,f1444])).

fof(f2440,plain,
    ( spl9_49
    | ~ spl9_55
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f1308,f1036,f211,f113,f108,f103,f98,f2437,f2409])).

fof(f2409,plain,
    ( spl9_49
  <=> r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f2437,plain,
    ( spl9_55
  <=> r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f1308,plain,
    ( ~ r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_24 ),
    inference(superposition,[],[f311,f1038])).

fof(f2435,plain,
    ( spl9_47
    | ~ spl9_54
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f1305,f1036,f211,f113,f108,f103,f98,f2432,f2400])).

fof(f2400,plain,
    ( spl9_47
  <=> r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f2432,plain,
    ( spl9_54
  <=> r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f1305,plain,
    ( ~ r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_24 ),
    inference(superposition,[],[f305,f1038])).

fof(f2430,plain,
    ( spl9_52
    | ~ spl9_53
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f1422,f1036,f981,f113,f108,f103,f98,f2427,f2423])).

fof(f2423,plain,
    ( spl9_52
  <=> r3_lattices(sK0,sK2(sK0),sK3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).

fof(f2427,plain,
    ( spl9_53
  <=> r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).

fof(f1422,plain,
    ( ~ r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK2(sK0)))
    | r3_lattices(sK0,sK2(sK0),sK3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23
    | ~ spl9_24 ),
    inference(superposition,[],[f1220,f1038])).

fof(f2421,plain,
    ( spl9_50
    | ~ spl9_51
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f1419,f1036,f981,f113,f108,f103,f98,f2418,f2414])).

fof(f2414,plain,
    ( spl9_50
  <=> r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f2418,plain,
    ( spl9_51
  <=> r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f1419,plain,
    ( ~ r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK2(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23
    | ~ spl9_24 ),
    inference(superposition,[],[f1219,f1038])).

fof(f2412,plain,
    ( ~ spl9_48
    | spl9_49
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f1292,f1036,f175,f113,f108,f103,f98,f2409,f2405])).

fof(f2405,plain,
    ( spl9_48
  <=> r1_tarski(a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_3_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f1292,plain,
    ( r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0))
    | ~ r1_tarski(a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_24 ),
    inference(superposition,[],[f225,f1038])).

fof(f2403,plain,
    ( ~ spl9_46
    | spl9_47
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f1291,f1036,f175,f113,f108,f103,f98,f2400,f2396])).

fof(f2396,plain,
    ( spl9_46
  <=> r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f1291,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_24 ),
    inference(superposition,[],[f221,f1038])).

fof(f2170,plain,
    ( spl9_45
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1994,f1442,f125,f113,f108,f103,f98,f2167])).

fof(f2167,plain,
    ( spl9_45
  <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).

fof(f1994,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(superposition,[],[f1897,f1444])).

fof(f2063,plain,
    ( spl9_44
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1896,f1442,f125,f113,f108,f103,f98,f2060])).

fof(f2060,plain,
    ( spl9_44
  <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f1896,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(superposition,[],[f1799,f1444])).

fof(f1927,plain,
    ( spl9_43
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1798,f1442,f125,f113,f108,f103,f98,f1924])).

fof(f1798,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_36 ),
    inference(superposition,[],[f1756,f1444])).

fof(f1829,plain,
    ( spl9_42
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f1797,f1036,f125,f113,f108,f103,f98,f1826])).

fof(f1797,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_24 ),
    inference(superposition,[],[f1756,f1038])).

fof(f1616,plain,
    ( spl9_41
    | ~ spl9_17
    | spl9_1
    | ~ spl9_15
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f1268,f1077,f409,f98,f416,f1614])).

fof(f1268,plain,
    ( ! [X0] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0) )
    | spl9_1
    | ~ spl9_15
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1267,f410])).

fof(f1267,plain,
    ( ! [X0] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0)
        | ~ v6_lattices(sK0) )
    | spl9_1
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1254,f100])).

fof(f1254,plain,
    ( ! [X0] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | k2_lattices(sK0,X0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0)
        | ~ v6_lattices(sK0) )
    | ~ spl9_25 ),
    inference(resolution,[],[f1079,f72])).

fof(f1607,plain,
    ( spl9_40
    | ~ spl9_19
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f1370,f1077,f700,f1604])).

fof(f1604,plain,
    ( spl9_40
  <=> k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f1370,plain,
    ( k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ spl9_19
    | ~ spl9_25 ),
    inference(resolution,[],[f701,f1079])).

fof(f1557,plain,
    ( spl9_39
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f1544,f1525,f1487,f113,f108,f103,f98,f1554])).

fof(f1554,plain,
    ( spl9_39
  <=> r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f1544,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1543,f100])).

fof(f1543,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_37
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1542,f1489])).

fof(f1542,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1541,f115])).

fof(f1541,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1540,f110])).

fof(f1540,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_38 ),
    inference(subsumption_resolution,[],[f1537,f105])).

fof(f1537,plain,
    ( r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_38 ),
    inference(superposition,[],[f94,f1527])).

fof(f1528,plain,
    ( spl9_38
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1455,f1442,f113,f108,f103,f98,f1525])).

fof(f1455,plain,
    ( sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_36 ),
    inference(superposition,[],[f281,f1444])).

fof(f1490,plain,
    ( spl9_37
    | spl9_1
    | ~ spl9_4
    | ~ spl9_36 ),
    inference(avatar_split_clause,[],[f1485,f1442,f113,f98,f1487])).

fof(f1485,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_36 ),
    inference(subsumption_resolution,[],[f1484,f100])).

fof(f1484,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_36 ),
    inference(subsumption_resolution,[],[f1475,f115])).

fof(f1475,plain,
    ( m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_36 ),
    inference(superposition,[],[f87,f1444])).

fof(f1445,plain,
    ( spl9_36
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f1281,f1077,f125,f113,f108,f103,f98,f1442])).

fof(f1281,plain,
    ( sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1280,f127])).

fof(f1280,plain,
    ( sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | v13_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1279,f105])).

fof(f1279,plain,
    ( sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ v10_lattices(sK0)
    | v13_lattices(sK0)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1278,f100])).

fof(f1278,plain,
    ( v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ v10_lattices(sK0)
    | v13_lattices(sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1277,f115])).

fof(f1277,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ v10_lattices(sK0)
    | v13_lattices(sK0)
    | ~ spl9_3
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1257,f110])).

fof(f1257,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))
    | ~ v10_lattices(sK0)
    | v13_lattices(sK0)
    | ~ spl9_25 ),
    inference(resolution,[],[f1079,f169])).

fof(f1416,plain,
    ( ~ spl9_34
    | spl9_35
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f1328,f981,f211,f113,f108,f103,f98,f1413,f1409])).

fof(f1409,plain,
    ( spl9_34
  <=> r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f1413,plain,
    ( spl9_35
  <=> r3_lattices(sK0,sK2(sK0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f1328,plain,
    ( r3_lattices(sK0,sK2(sK0),k5_lattices(sK0))
    | ~ r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK2(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_23 ),
    inference(superposition,[],[f1238,f213])).

fof(f1238,plain,
    ( ! [X3] :
        ( r3_lattices(sK0,sK2(sK0),k16_lattice3(sK0,X3))
        | ~ r1_tarski(X3,a_2_4_lattice3(sK0,sK2(sK0))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1237,f100])).

fof(f1237,plain,
    ( ! [X3] :
        ( r3_lattices(sK0,sK2(sK0),k16_lattice3(sK0,X3))
        | ~ r1_tarski(X3,a_2_4_lattice3(sK0,sK2(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1236,f115])).

fof(f1236,plain,
    ( ! [X3] :
        ( r3_lattices(sK0,sK2(sK0),k16_lattice3(sK0,X3))
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X3,a_2_4_lattice3(sK0,sK2(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1235,f110])).

fof(f1235,plain,
    ( ! [X3] :
        ( r3_lattices(sK0,sK2(sK0),k16_lattice3(sK0,X3))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X3,a_2_4_lattice3(sK0,sK2(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1225,f105])).

fof(f1225,plain,
    ( ! [X3] :
        ( r3_lattices(sK0,sK2(sK0),k16_lattice3(sK0,X3))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X3,a_2_4_lattice3(sK0,sK2(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_23 ),
    inference(superposition,[],[f82,f983])).

fof(f1407,plain,
    ( ~ spl9_32
    | spl9_33
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f1325,f981,f211,f113,f108,f103,f98,f1404,f1400])).

fof(f1400,plain,
    ( spl9_32
  <=> r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f1404,plain,
    ( spl9_33
  <=> r3_lattices(sK0,k5_lattices(sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f1325,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),sK2(sK0))
    | ~ r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_23 ),
    inference(superposition,[],[f1234,f213])).

fof(f1234,plain,
    ( ! [X2] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X2),sK2(sK0))
        | ~ r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),X2) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1233,f100])).

fof(f1233,plain,
    ( ! [X2] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X2),sK2(sK0))
        | ~ r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),X2)
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1232,f115])).

fof(f1232,plain,
    ( ! [X2] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X2),sK2(sK0))
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),X2)
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1231,f110])).

fof(f1231,plain,
    ( ! [X2] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X2),sK2(sK0))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),X2)
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1224,f105])).

fof(f1224,plain,
    ( ! [X2] :
        ( r3_lattices(sK0,k16_lattice3(sK0,X2),sK2(sK0))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),X2)
        | v2_struct_0(sK0) )
    | ~ spl9_23 ),
    inference(superposition,[],[f82,f983])).

fof(f1398,plain,
    ( ~ spl9_30
    | spl9_31
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f1327,f981,f113,f108,f103,f98,f1395,f1391])).

fof(f1391,plain,
    ( spl9_30
  <=> r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f1327,plain,
    ( r3_lattices(sK0,sK2(sK0),sK2(sK0))
    | ~ r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK2(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(superposition,[],[f1234,f983])).

fof(f1364,plain,
    ( spl9_29
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24
    | ~ spl9_25 ),
    inference(avatar_split_clause,[],[f1316,f1077,f1036,f113,f108,f103,f98,f1361])).

fof(f1316,plain,
    ( r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24
    | ~ spl9_25 ),
    inference(subsumption_resolution,[],[f1309,f1079])).

fof(f1309,plain,
    ( r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(superposition,[],[f333,f1038])).

fof(f1337,plain,
    ( spl9_28
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f1049,f1036,f113,f108,f103,f98,f1334])).

fof(f1049,plain,
    ( sK3(sK0,k5_lattices(sK0)) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(superposition,[],[f281,f1038])).

fof(f1331,plain,
    ( ~ spl9_20
    | spl9_27
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f1290,f981,f113,f108,f103,f98,f1286,f811])).

fof(f1286,plain,
    ( spl9_27
  <=> r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f1290,plain,
    ( r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0)))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1228,f100])).

fof(f1228,plain,
    ( r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0)))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1227,f115])).

fof(f1227,plain,
    ( r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0)))
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1226,f110])).

fof(f1226,plain,
    ( r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_23 ),
    inference(subsumption_resolution,[],[f1223,f105])).

fof(f1223,plain,
    ( r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0)))
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_23 ),
    inference(superposition,[],[f94,f983])).

fof(f1289,plain,
    ( spl9_27
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f966,f811,f274,f113,f108,f103,f98,f1286])).

fof(f966,plain,
    ( r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f959,f813])).

fof(f959,plain,
    ( r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0)))
    | ~ m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(superposition,[],[f333,f276])).

fof(f1243,plain,
    ( ~ spl9_17
    | spl9_26
    | spl9_1
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f1124,f125,f98,f1240,f416])).

fof(f1124,plain,
    ( sK2(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0))
    | ~ l1_lattices(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f1090,f100])).

fof(f1090,plain,
    ( v2_struct_0(sK0)
    | sK2(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0))
    | ~ l1_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f126,f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v13_lattices(X0)
      | v2_struct_0(X0)
      | sK2(X0) = k2_lattices(X0,sK2(X0),k5_lattices(X0))
      | ~ l1_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | sK2(X0) = k2_lattices(X0,sK2(X0),k5_lattices(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f65,f60])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | sK2(X0) = k2_lattices(X0,sK2(X0),X2)
      | ~ v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1080,plain,
    ( spl9_25
    | spl9_1
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f1075,f1036,f113,f98,f1077])).

fof(f1075,plain,
    ( m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f1074,f100])).

fof(f1074,plain,
    ( m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f1065,f115])).

fof(f1065,plain,
    ( m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_24 ),
    inference(superposition,[],[f87,f1038])).

fof(f1039,plain,
    ( spl9_24
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f1034,f183,f125,f113,f108,f103,f98,f1036])).

fof(f1034,plain,
    ( sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f1033,f127])).

fof(f1033,plain,
    ( sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | v13_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f1032,f105])).

fof(f1032,plain,
    ( sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ v10_lattices(sK0)
    | v13_lattices(sK0)
    | spl9_1
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f1031,f100])).

fof(f1031,plain,
    ( v2_struct_0(sK0)
    | sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ v10_lattices(sK0)
    | v13_lattices(sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f1030,f115])).

fof(f1030,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ v10_lattices(sK0)
    | v13_lattices(sK0)
    | ~ spl9_3
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f1017,f110])).

fof(f1017,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))
    | ~ v10_lattices(sK0)
    | v13_lattices(sK0)
    | ~ spl9_8 ),
    inference(resolution,[],[f169,f185])).

fof(f986,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_10
    | ~ spl9_20 ),
    inference(avatar_contradiction_clause,[],[f985])).

fof(f985,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_10
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f931,f275])).

fof(f275,plain,
    ( sK2(sK0) != k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))
    | spl9_10 ),
    inference(avatar_component_clause,[],[f274])).

fof(f931,plain,
    ( sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f930,f100])).

fof(f930,plain,
    ( v2_struct_0(sK0)
    | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f929,f115])).

fof(f929,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f928,f110])).

fof(f928,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))
    | ~ spl9_2
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f915,f105])).

fof(f915,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))
    | ~ spl9_20 ),
    inference(resolution,[],[f813,f74])).

fof(f984,plain,
    ( spl9_23
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f784,f274,f113,f108,f103,f98,f981])).

fof(f784,plain,
    ( sK2(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK2(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(superposition,[],[f281,f276])).

fof(f979,plain,
    ( ~ spl9_17
    | spl9_22
    | spl9_1
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f880,f125,f98,f976,f416])).

fof(f976,plain,
    ( spl9_22
  <=> sK2(sK0) = k2_lattices(sK0,sK2(sK0),sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f880,plain,
    ( sK2(sK0) = k2_lattices(sK0,sK2(sK0),sK2(sK0))
    | ~ l1_lattices(sK0)
    | spl9_1
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f846,f100])).

fof(f846,plain,
    ( v2_struct_0(sK0)
    | sK2(sK0) = k2_lattices(sK0,sK2(sK0),sK2(sK0))
    | ~ l1_lattices(sK0)
    | ~ spl9_6 ),
    inference(resolution,[],[f126,f138])).

fof(f138,plain,(
    ! [X3] :
      ( ~ v13_lattices(X3)
      | v2_struct_0(X3)
      | sK2(X3) = k2_lattices(X3,sK2(X3),sK2(X3))
      | ~ l1_lattices(X3) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X3] :
      ( ~ l1_lattices(X3)
      | v2_struct_0(X3)
      | sK2(X3) = k2_lattices(X3,sK2(X3),sK2(X3))
      | ~ v13_lattices(X3)
      | ~ l1_lattices(X3)
      | v2_struct_0(X3)
      | ~ v13_lattices(X3) ) ),
    inference(resolution,[],[f65,f69])).

fof(f840,plain,
    ( spl9_21
    | ~ spl9_8
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f815,f700,f183,f837])).

fof(f815,plain,
    ( k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))
    | ~ spl9_8
    | ~ spl9_19 ),
    inference(resolution,[],[f701,f185])).

fof(f814,plain,
    ( spl9_20
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f809,f274,f113,f98,f811])).

fof(f809,plain,
    ( m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f808,f100])).

fof(f808,plain,
    ( m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f799,f115])).

fof(f799,plain,
    ( m1_subset_1(sK2(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_10 ),
    inference(superposition,[],[f87,f276])).

fof(f702,plain,
    ( ~ spl9_17
    | spl9_19
    | spl9_1
    | spl9_6
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f438,f413,f125,f98,f700,f416])).

fof(f438,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,X2),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,X2))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | spl9_1
    | spl9_6
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f437,f127])).

fof(f437,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,X2),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,X2))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v13_lattices(sK0) )
    | spl9_1
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f433,f100])).

fof(f433,plain,
    ( ! [X2] :
        ( k2_lattices(sK0,sK3(sK0,X2),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,X2))
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | v13_lattices(sK0) )
    | ~ spl9_16 ),
    inference(resolution,[],[f414,f68])).

fof(f447,plain,
    ( spl9_15
    | ~ spl9_17
    | spl9_18
    | spl9_1
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f439,f413,f98,f444,f416,f409])).

fof(f444,plain,
    ( spl9_18
  <=> k2_lattices(sK0,sK4(sK0),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f439,plain,
    ( k2_lattices(sK0,sK4(sK0),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0))
    | ~ l1_lattices(sK0)
    | v6_lattices(sK0)
    | spl9_1
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f434,f100])).

fof(f434,plain,
    ( k2_lattices(sK0,sK4(sK0),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | v6_lattices(sK0)
    | ~ spl9_16 ),
    inference(resolution,[],[f414,f73])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f427,plain,
    ( ~ spl9_4
    | spl9_17 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl9_4
    | spl9_17 ),
    inference(subsumption_resolution,[],[f425,f115])).

fof(f425,plain,
    ( ~ l3_lattices(sK0)
    | spl9_17 ),
    inference(resolution,[],[f418,f50])).

fof(f418,plain,
    ( ~ l1_lattices(sK0)
    | spl9_17 ),
    inference(avatar_component_clause,[],[f416])).

fof(f424,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_15 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_15 ),
    inference(subsumption_resolution,[],[f422,f115])).

fof(f422,plain,
    ( ~ l3_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | spl9_15 ),
    inference(subsumption_resolution,[],[f421,f105])).

fof(f421,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_1
    | spl9_15 ),
    inference(subsumption_resolution,[],[f420,f100])).

fof(f420,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | spl9_15 ),
    inference(resolution,[],[f411,f54])).

fof(f411,plain,
    ( ~ v6_lattices(sK0)
    | spl9_15 ),
    inference(avatar_component_clause,[],[f409])).

fof(f419,plain,
    ( ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | spl9_1
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f382,f183,f98,f416,f413,f409])).

fof(f382,plain,
    ( ! [X21] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | k2_lattices(sK0,X21,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X21)
        | ~ v6_lattices(sK0) )
    | spl9_1
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f371,f100])).

fof(f371,plain,
    ( ! [X21] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | k2_lattices(sK0,X21,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X21)
        | ~ v6_lattices(sK0) )
    | ~ spl9_8 ),
    inference(resolution,[],[f72,f185])).

fof(f354,plain,
    ( ~ spl9_14
    | spl9_13
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f238,f211,f113,f108,f103,f98,f346,f351])).

fof(f351,plain,
    ( spl9_14
  <=> r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f238,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(superposition,[],[f233,f213])).

fof(f233,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))
        | ~ r1_tarski(X0,a_2_4_lattice3(sK0,k5_lattices(sK0))) )
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f232,f100])).

fof(f232,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))
        | ~ r1_tarski(X0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f231,f115])).

fof(f231,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f230,f110])).

fof(f230,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f228,f105])).

fof(f228,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))
        | ~ v10_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ l3_lattices(sK0)
        | ~ r1_tarski(X0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl9_9 ),
    inference(superposition,[],[f82,f213])).

fof(f349,plain,
    ( ~ spl9_12
    | spl9_13
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f226,f175,f113,f108,f103,f98,f346,f342])).

fof(f342,plain,
    ( spl9_12
  <=> r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,k5_lattices(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f226,plain,
    ( r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))
    | ~ r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(superposition,[],[f221,f177])).

fof(f338,plain,
    ( spl9_11
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f329,f211,f183,f113,f108,f103,f98,f335])).

fof(f329,plain,
    ( r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f328,f100])).

fof(f328,plain,
    ( r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f327,f185])).

fof(f327,plain,
    ( r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f326,f115])).

fof(f326,plain,
    ( r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f325,f110])).

fof(f325,plain,
    ( r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_2
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f323,f105])).

fof(f323,plain,
    ( r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_9 ),
    inference(superposition,[],[f94,f213])).

fof(f277,plain,
    ( ~ spl9_6
    | spl9_10
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f272,f113,f108,f103,f98,f274,f125])).

fof(f272,plain,
    ( sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))
    | ~ v13_lattices(sK0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f271,f100])).

fof(f271,plain,
    ( v2_struct_0(sK0)
    | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))
    | ~ v13_lattices(sK0)
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f270,f115])).

fof(f270,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))
    | ~ v13_lattices(sK0)
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f269,f105])).

fof(f269,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))
    | ~ v13_lattices(sK0)
    | ~ spl9_3 ),
    inference(resolution,[],[f168,f110])).

fof(f168,plain,(
    ! [X3] :
      ( ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | sK2(X3) = k15_lattice3(X3,a_2_3_lattice3(X3,sK2(X3)))
      | ~ v13_lattices(X3) ) ),
    inference(subsumption_resolution,[],[f164,f50])).

fof(f164,plain,(
    ! [X3] :
      ( ~ v10_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | sK2(X3) = k15_lattice3(X3,a_2_3_lattice3(X3,sK2(X3)))
      | ~ l1_lattices(X3)
      | ~ v13_lattices(X3) ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X3] :
      ( ~ v10_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | sK2(X3) = k15_lattice3(X3,a_2_3_lattice3(X3,sK2(X3)))
      | ~ l1_lattices(X3)
      | v2_struct_0(X3)
      | ~ v13_lattices(X3) ) ),
    inference(resolution,[],[f74,f69])).

fof(f214,plain,
    ( spl9_9
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f209,f183,f113,f108,f103,f98,f211])).

fof(f209,plain,
    ( k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f208,f100])).

fof(f208,plain,
    ( v2_struct_0(sK0)
    | k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f207,f115])).

fof(f207,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f206,f110])).

fof(f206,plain,
    ( ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_2
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f196,f105])).

fof(f196,plain,
    ( ~ v10_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_8 ),
    inference(resolution,[],[f75,f185])).

fof(f186,plain,
    ( spl9_8
    | spl9_1
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f181,f175,f113,f98,f183])).

fof(f181,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f180,f100])).

fof(f180,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f179,f115])).

fof(f179,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl9_7 ),
    inference(superposition,[],[f87,f177])).

fof(f178,plain,
    ( spl9_7
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f173,f113,f108,f103,f98,f175])).

fof(f173,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f172,f100])).

fof(f172,plain,
    ( v2_struct_0(sK0)
    | k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f171,f115])).

fof(f171,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f170,f105])).

fof(f170,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl9_3 ),
    inference(resolution,[],[f167,f110])).

fof(f167,plain,(
    ! [X0] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k5_lattices(X0) = k15_lattice3(X0,a_2_3_lattice3(X0,k5_lattices(X0))) ) ),
    inference(subsumption_resolution,[],[f166,f50])).

fof(f166,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k5_lattices(X0) = k15_lattice3(X0,a_2_3_lattice3(X0,k5_lattices(X0)))
      | ~ l1_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | k5_lattices(X0) = k15_lattice3(X0,a_2_3_lattice3(X0,k5_lattices(X0)))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f74,f60])).

fof(f128,plain,
    ( ~ spl9_5
    | ~ spl9_6
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f119,f113,f103,f98,f125,f121])).

fof(f119,plain,
    ( ~ v13_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f118,f115])).

fof(f118,plain,
    ( ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f117,f105])).

fof(f117,plain,
    ( ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f44,f100])).

fof(f44,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ l3_lattices(sK0)
    | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(f116,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f48,f113])).

fof(f48,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f111,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f47,f108])).

fof(f47,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f106,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f46,f103])).

fof(f46,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f101,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f45,f98])).

fof(f45,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:36:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (28804)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.47  % (28802)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.48  % (28802)Refutation not found, incomplete strategy% (28802)------------------------------
% 0.22/0.48  % (28802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (28819)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.48  % (28802)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (28802)Memory used [KB]: 10618
% 0.22/0.48  % (28802)Time elapsed: 0.061 s
% 0.22/0.48  % (28802)------------------------------
% 0.22/0.48  % (28802)------------------------------
% 0.22/0.49  % (28801)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.49  % (28821)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.49  % (28801)Refutation not found, incomplete strategy% (28801)------------------------------
% 0.22/0.49  % (28801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28801)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (28801)Memory used [KB]: 10490
% 0.22/0.49  % (28801)Time elapsed: 0.002 s
% 0.22/0.49  % (28801)------------------------------
% 0.22/0.49  % (28801)------------------------------
% 0.22/0.49  % (28803)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.49  % (28813)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.50  % (28809)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (28807)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (28807)Refutation not found, incomplete strategy% (28807)------------------------------
% 0.22/0.50  % (28807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28807)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28807)Memory used [KB]: 10490
% 0.22/0.50  % (28807)Time elapsed: 0.001 s
% 0.22/0.50  % (28807)------------------------------
% 0.22/0.50  % (28807)------------------------------
% 0.22/0.50  % (28825)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (28824)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.50  % (28820)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.50  % (28827)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.50  % (28810)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (28805)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (28808)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (28811)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (28814)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (28815)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (28814)Refutation not found, incomplete strategy% (28814)------------------------------
% 0.22/0.51  % (28814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28814)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28814)Memory used [KB]: 6140
% 0.22/0.51  % (28814)Time elapsed: 0.071 s
% 0.22/0.51  % (28814)------------------------------
% 0.22/0.51  % (28814)------------------------------
% 0.22/0.51  % (28826)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (28817)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (28823)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (28818)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (28812)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (28812)Refutation not found, incomplete strategy% (28812)------------------------------
% 0.22/0.52  % (28812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28812)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28812)Memory used [KB]: 10490
% 0.22/0.52  % (28812)Time elapsed: 0.003 s
% 0.22/0.52  % (28812)------------------------------
% 0.22/0.52  % (28812)------------------------------
% 0.22/0.52  % (28806)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (28808)Refutation not found, incomplete strategy% (28808)------------------------------
% 0.22/0.53  % (28808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28808)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28808)Memory used [KB]: 1791
% 0.22/0.53  % (28808)Time elapsed: 0.116 s
% 0.22/0.53  % (28808)------------------------------
% 0.22/0.53  % (28808)------------------------------
% 0.22/0.53  % (28822)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.92/0.62  % (28810)Refutation not found, incomplete strategy% (28810)------------------------------
% 1.92/0.62  % (28810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.62  % (28810)Termination reason: Refutation not found, incomplete strategy
% 1.92/0.62  
% 1.92/0.62  % (28810)Memory used [KB]: 6140
% 1.92/0.62  % (28810)Time elapsed: 0.206 s
% 1.92/0.62  % (28810)------------------------------
% 1.92/0.62  % (28810)------------------------------
% 4.32/0.92  % (28815)Time limit reached!
% 4.32/0.92  % (28815)------------------------------
% 4.32/0.92  % (28815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.32/0.92  % (28815)Termination reason: Time limit
% 4.32/0.92  % (28815)Termination phase: Saturation
% 4.32/0.92  
% 4.32/0.92  % (28815)Memory used [KB]: 10746
% 4.32/0.92  % (28815)Time elapsed: 0.500 s
% 4.32/0.92  % (28815)------------------------------
% 4.32/0.92  % (28815)------------------------------
% 5.81/1.13  % (28826)Refutation found. Thanks to Tanya!
% 5.81/1.13  % SZS status Theorem for theBenchmark
% 5.81/1.13  % SZS output start Proof for theBenchmark
% 5.81/1.13  fof(f9767,plain,(
% 5.81/1.13    $false),
% 5.81/1.13    inference(avatar_sat_refutation,[],[f101,f106,f111,f116,f128,f178,f186,f214,f277,f338,f349,f354,f419,f424,f427,f447,f702,f814,f840,f979,f984,f986,f1039,f1080,f1243,f1289,f1331,f1337,f1364,f1398,f1407,f1416,f1445,f1490,f1528,f1557,f1607,f1616,f1829,f1927,f2063,f2170,f2403,f2412,f2421,f2430,f2435,f2440,f2445,f2549,f2674,f2685,f2708,f2791,f2798,f2802,f2805,f2924,f2999,f3032,f3289,f3357,f3362,f3367,f3524,f3541,f3548,f3551,f3562,f3575,f3582,f3585,f3596,f3666,f3676,f3691,f3696,f3707,f3722,f3928,f3942,f3952,f3959,f4010,f4024,f4034,f4041,f4053,f4122,f4134,f4179,f4191,f4227,f4244,f4259,f4409,f4829,f4894,f4912,f4924,f4997,f5065,f5076,f5106,f6108,f6266,f6275,f6280,f6285,f6294,f6303,f6333,f6340,f6433,f6453,f6634,f6876,f7027,f7032,f7056,f7098,f7279,f7393,f7432,f7518,f7932,f8801,f8838,f9525,f9659,f9671,f9686,f9703,f9725,f9763])).
% 5.81/1.13  fof(f9763,plain,(
% 5.81/1.13    spl9_1 | ~spl9_4 | spl9_5 | ~spl9_6 | ~spl9_137),
% 5.81/1.13    inference(avatar_contradiction_clause,[],[f9762])).
% 5.81/1.13  fof(f9762,plain,(
% 5.81/1.13    $false | (spl9_1 | ~spl9_4 | spl9_5 | ~spl9_6 | ~spl9_137)),
% 5.81/1.13    inference(subsumption_resolution,[],[f9754,f123])).
% 5.81/1.13  fof(f123,plain,(
% 5.81/1.13    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl9_5),
% 5.81/1.13    inference(avatar_component_clause,[],[f121])).
% 5.81/1.13  fof(f121,plain,(
% 5.81/1.13    spl9_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 5.81/1.13  fof(f9754,plain,(
% 5.81/1.13    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (spl9_1 | ~spl9_4 | ~spl9_6 | ~spl9_137)),
% 5.81/1.13    inference(backward_demodulation,[],[f8800,f9384])).
% 5.81/1.13  fof(f9384,plain,(
% 5.81/1.13    ( ! [X2] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0))) ) | (spl9_1 | ~spl9_4 | ~spl9_6)),
% 5.81/1.13    inference(subsumption_resolution,[],[f9383,f115])).
% 5.81/1.13  fof(f115,plain,(
% 5.81/1.13    l3_lattices(sK0) | ~spl9_4),
% 5.81/1.13    inference(avatar_component_clause,[],[f113])).
% 5.81/1.13  fof(f113,plain,(
% 5.81/1.13    spl9_4 <=> l3_lattices(sK0)),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 5.81/1.13  fof(f9383,plain,(
% 5.81/1.13    ( ! [X2] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0)) | ~l3_lattices(sK0)) ) | (spl9_1 | ~spl9_6)),
% 5.81/1.13    inference(subsumption_resolution,[],[f9350,f100])).
% 5.81/1.13  fof(f100,plain,(
% 5.81/1.13    ~v2_struct_0(sK0) | spl9_1),
% 5.81/1.13    inference(avatar_component_clause,[],[f98])).
% 5.81/1.13  fof(f98,plain,(
% 5.81/1.13    spl9_1 <=> v2_struct_0(sK0)),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 5.81/1.13  fof(f9350,plain,(
% 5.81/1.13    ( ! [X2] : (v2_struct_0(sK0) | k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X2),k5_lattices(sK0)) | ~l3_lattices(sK0)) ) | ~spl9_6),
% 5.81/1.13    inference(resolution,[],[f126,f479])).
% 5.81/1.13  fof(f479,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~v13_lattices(X1) | v2_struct_0(X1) | k5_lattices(X1) = k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1)) | ~l3_lattices(X1)) )),
% 5.81/1.13    inference(subsumption_resolution,[],[f477,f50])).
% 5.81/1.13  fof(f50,plain,(
% 5.81/1.13    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f19])).
% 5.81/1.13  fof(f19,plain,(
% 5.81/1.13    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 5.81/1.13    inference(ennf_transformation,[],[f5])).
% 5.81/1.13  fof(f5,axiom,(
% 5.81/1.13    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 5.81/1.13  fof(f477,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~l1_lattices(X1) | ~v13_lattices(X1) | v2_struct_0(X1) | k5_lattices(X1) = k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1)) | ~l3_lattices(X1)) )),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f463])).
% 5.81/1.13  fof(f463,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~l1_lattices(X1) | ~v13_lattices(X1) | v2_struct_0(X1) | k5_lattices(X1) = k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 5.81/1.13    inference(resolution,[],[f461,f87])).
% 5.81/1.13  fof(f87,plain,(
% 5.81/1.13    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f41])).
% 5.81/1.13  fof(f41,plain,(
% 5.81/1.13    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.81/1.13    inference(flattening,[],[f40])).
% 5.81/1.13  fof(f40,plain,(
% 5.81/1.13    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 5.81/1.13    inference(ennf_transformation,[],[f10])).
% 5.81/1.13  fof(f10,axiom,(
% 5.81/1.13    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 5.81/1.13  fof(f461,plain,(
% 5.81/1.13    ( ! [X2,X0] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v13_lattices(X0) | v2_struct_0(X0) | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0))) )),
% 5.81/1.13    inference(subsumption_resolution,[],[f92,f60])).
% 5.81/1.13  fof(f60,plain,(
% 5.81/1.13    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f25])).
% 5.81/1.13  fof(f25,plain,(
% 5.81/1.13    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.81/1.13    inference(flattening,[],[f24])).
% 5.81/1.13  fof(f24,plain,(
% 5.81/1.13    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 5.81/1.13    inference(ennf_transformation,[],[f4])).
% 5.81/1.13  fof(f4,axiom,(
% 5.81/1.13    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 5.81/1.13  fof(f92,plain,(
% 5.81/1.13    ( ! [X2,X0] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,X2,k5_lattices(X0))) )),
% 5.81/1.13    inference(equality_resolution,[],[f63])).
% 5.81/1.13  fof(f63,plain,(
% 5.81/1.13    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X2,X1) = X1 | k5_lattices(X0) != X1) )),
% 5.81/1.13    inference(cnf_transformation,[],[f27])).
% 5.81/1.13  fof(f27,plain,(
% 5.81/1.13    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.81/1.13    inference(flattening,[],[f26])).
% 5.81/1.13  fof(f26,plain,(
% 5.81/1.13    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 5.81/1.13    inference(ennf_transformation,[],[f3])).
% 5.81/1.13  fof(f3,axiom,(
% 5.81/1.13    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 5.81/1.13  fof(f126,plain,(
% 5.81/1.13    v13_lattices(sK0) | ~spl9_6),
% 5.81/1.13    inference(avatar_component_clause,[],[f125])).
% 5.81/1.13  fof(f125,plain,(
% 5.81/1.13    spl9_6 <=> v13_lattices(sK0)),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 5.81/1.13  fof(f8800,plain,(
% 5.81/1.13    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl9_137),
% 5.81/1.13    inference(avatar_component_clause,[],[f8798])).
% 5.81/1.13  fof(f8798,plain,(
% 5.81/1.13    spl9_137 <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_137])])).
% 5.81/1.13  fof(f9725,plain,(
% 5.81/1.13    ~spl9_17 | spl9_141 | spl9_1 | ~spl9_6 | ~spl9_26),
% 5.81/1.13    inference(avatar_split_clause,[],[f9720,f1240,f125,f98,f9722,f416])).
% 5.81/1.13  fof(f416,plain,(
% 5.81/1.13    spl9_17 <=> l1_lattices(sK0)),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 5.81/1.13  fof(f9722,plain,(
% 5.81/1.13    spl9_141 <=> k5_lattices(sK0) = sK2(sK0)),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_141])])).
% 5.81/1.13  fof(f1240,plain,(
% 5.81/1.13    spl9_26 <=> sK2(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 5.81/1.13  fof(f9720,plain,(
% 5.81/1.13    k5_lattices(sK0) = sK2(sK0) | ~l1_lattices(sK0) | (spl9_1 | ~spl9_6 | ~spl9_26)),
% 5.81/1.13    inference(forward_demodulation,[],[f9382,f1242])).
% 5.81/1.13  fof(f1242,plain,(
% 5.81/1.13    sK2(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0)) | ~spl9_26),
% 5.81/1.13    inference(avatar_component_clause,[],[f1240])).
% 5.81/1.13  fof(f9382,plain,(
% 5.81/1.13    ~l1_lattices(sK0) | k5_lattices(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0)) | (spl9_1 | ~spl9_6)),
% 5.81/1.13    inference(subsumption_resolution,[],[f9348,f100])).
% 5.81/1.13  fof(f9348,plain,(
% 5.81/1.13    ~l1_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0)) | ~spl9_6),
% 5.81/1.13    inference(resolution,[],[f126,f475])).
% 5.81/1.13  fof(f475,plain,(
% 5.81/1.13    ( ! [X5] : (~v13_lattices(X5) | ~l1_lattices(X5) | v2_struct_0(X5) | k5_lattices(X5) = k2_lattices(X5,sK2(X5),k5_lattices(X5))) )),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f465])).
% 5.81/1.13  fof(f465,plain,(
% 5.81/1.13    ( ! [X5] : (~l1_lattices(X5) | ~v13_lattices(X5) | v2_struct_0(X5) | k5_lattices(X5) = k2_lattices(X5,sK2(X5),k5_lattices(X5)) | ~l1_lattices(X5) | v2_struct_0(X5) | ~v13_lattices(X5)) )),
% 5.81/1.13    inference(resolution,[],[f461,f69])).
% 5.81/1.13  fof(f69,plain,(
% 5.81/1.13    ( ! [X0] : (m1_subset_1(sK2(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0) | ~v13_lattices(X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f29])).
% 5.81/1.13  fof(f29,plain,(
% 5.81/1.13    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.81/1.13    inference(flattening,[],[f28])).
% 5.81/1.13  fof(f28,plain,(
% 5.81/1.13    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 5.81/1.13    inference(ennf_transformation,[],[f7])).
% 5.81/1.13  fof(f7,axiom,(
% 5.81/1.13    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 5.81/1.13  fof(f9703,plain,(
% 5.81/1.13    ~spl9_17 | spl9_140 | spl9_1 | ~spl9_6),
% 5.81/1.13    inference(avatar_split_clause,[],[f9377,f125,f98,f9700,f416])).
% 5.81/1.13  fof(f9700,plain,(
% 5.81/1.13    spl9_140 <=> sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_140])])).
% 5.81/1.13  fof(f9377,plain,(
% 5.81/1.13    sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0)) | ~l1_lattices(sK0) | (spl9_1 | ~spl9_6)),
% 5.81/1.13    inference(subsumption_resolution,[],[f9343,f100])).
% 5.81/1.13  fof(f9343,plain,(
% 5.81/1.13    v2_struct_0(sK0) | sK2(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK2(sK0)) | ~l1_lattices(sK0) | ~spl9_6),
% 5.81/1.13    inference(resolution,[],[f126,f153])).
% 5.81/1.13  fof(f153,plain,(
% 5.81/1.13    ( ! [X0] : (~v13_lattices(X0) | v2_struct_0(X0) | sK2(X0) = k2_lattices(X0,k5_lattices(X0),sK2(X0)) | ~l1_lattices(X0)) )),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f142])).
% 5.81/1.13  fof(f142,plain,(
% 5.81/1.13    ( ! [X0] : (~l1_lattices(X0) | v2_struct_0(X0) | sK2(X0) = k2_lattices(X0,k5_lattices(X0),sK2(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.81/1.13    inference(resolution,[],[f66,f60])).
% 5.81/1.13  fof(f66,plain,(
% 5.81/1.13    ( ! [X2,X0] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0) | sK2(X0) = k2_lattices(X0,X2,sK2(X0)) | ~v13_lattices(X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f29])).
% 5.81/1.13  fof(f9686,plain,(
% 5.81/1.13    ~spl9_139 | ~spl9_57 | spl9_127),
% 5.81/1.13    inference(avatar_split_clause,[],[f9674,f7024,f2546,f9683])).
% 5.81/1.13  fof(f9683,plain,(
% 5.81/1.13    spl9_139 <=> k5_lattices(sK0) = sK3(sK0,k5_lattices(sK0))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_139])])).
% 5.81/1.13  fof(f2546,plain,(
% 5.81/1.13    spl9_57 <=> k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).
% 5.81/1.13  fof(f7024,plain,(
% 5.81/1.13    spl9_127 <=> sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).
% 5.81/1.13  fof(f9674,plain,(
% 5.81/1.13    k5_lattices(sK0) != sK3(sK0,k5_lattices(sK0)) | (~spl9_57 | spl9_127)),
% 5.81/1.13    inference(backward_demodulation,[],[f7026,f2547])).
% 5.81/1.13  fof(f2547,plain,(
% 5.81/1.13    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~spl9_57),
% 5.81/1.13    inference(avatar_component_clause,[],[f2546])).
% 5.81/1.13  fof(f7026,plain,(
% 5.81/1.13    sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | spl9_127),
% 5.81/1.13    inference(avatar_component_clause,[],[f7024])).
% 5.81/1.13  fof(f9671,plain,(
% 5.81/1.13    spl9_138 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_10 | ~spl9_20),
% 5.81/1.13    inference(avatar_split_clause,[],[f9637,f811,f274,f113,f108,f103,f98,f9668])).
% 5.81/1.13  fof(f9668,plain,(
% 5.81/1.13    spl9_138 <=> r1_lattices(sK0,sK2(sK0),sK2(sK0))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_138])])).
% 5.81/1.13  fof(f103,plain,(
% 5.81/1.13    spl9_2 <=> v10_lattices(sK0)),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 5.81/1.13  fof(f108,plain,(
% 5.81/1.13    spl9_3 <=> v4_lattice3(sK0)),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 5.81/1.13  fof(f274,plain,(
% 5.81/1.13    spl9_10 <=> sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0)))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 5.81/1.13  fof(f811,plain,(
% 5.81/1.13    spl9_20 <=> m1_subset_1(sK2(sK0),u1_struct_0(sK0))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 5.81/1.13  fof(f9637,plain,(
% 5.81/1.13    r1_lattices(sK0,sK2(sK0),sK2(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_10 | ~spl9_20)),
% 5.81/1.13    inference(subsumption_resolution,[],[f9599,f813])).
% 5.81/1.13  fof(f813,plain,(
% 5.81/1.13    m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | ~spl9_20),
% 5.81/1.13    inference(avatar_component_clause,[],[f811])).
% 5.81/1.13  fof(f9599,plain,(
% 5.81/1.13    r1_lattices(sK0,sK2(sK0),sK2(sK0)) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_10)),
% 5.81/1.13    inference(superposition,[],[f4369,f276])).
% 5.81/1.13  fof(f276,plain,(
% 5.81/1.13    sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) | ~spl9_10),
% 5.81/1.13    inference(avatar_component_clause,[],[f274])).
% 5.81/1.13  fof(f4369,plain,(
% 5.81/1.13    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f4359])).
% 5.81/1.13  fof(f4359,plain,(
% 5.81/1.13    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(resolution,[],[f4343,f3280])).
% 5.81/1.13  fof(f3280,plain,(
% 5.81/1.13    ( ! [X4,X3] : (~r3_lattices(sK0,k15_lattice3(sK0,X3),X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X3),X4) | ~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3279,f100])).
% 5.81/1.13  fof(f3279,plain,(
% 5.81/1.13    ( ! [X4,X3] : (~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X3),X4) | ~r3_lattices(sK0,k15_lattice3(sK0,X3),X4) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3278,f115])).
% 5.81/1.13  fof(f3278,plain,(
% 5.81/1.13    ( ! [X4,X3] : (~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X3),X4) | ~l3_lattices(sK0) | ~r3_lattices(sK0,k15_lattice3(sK0,X3),X4) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3277,f110])).
% 5.81/1.13  fof(f110,plain,(
% 5.81/1.13    v4_lattice3(sK0) | ~spl9_3),
% 5.81/1.13    inference(avatar_component_clause,[],[f108])).
% 5.81/1.13  fof(f3277,plain,(
% 5.81/1.13    ( ! [X4,X3] : (~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X3),X4) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r3_lattices(sK0,k15_lattice3(sK0,X3),X4) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3276,f105])).
% 5.81/1.13  fof(f105,plain,(
% 5.81/1.13    v10_lattices(sK0) | ~spl9_2),
% 5.81/1.13    inference(avatar_component_clause,[],[f103])).
% 5.81/1.13  fof(f3276,plain,(
% 5.81/1.13    ( ! [X4,X3] : (~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X3),X4) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r3_lattices(sK0,k15_lattice3(sK0,X3),X4) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f3267])).
% 5.81/1.13  fof(f3267,plain,(
% 5.81/1.13    ( ! [X4,X3] : (~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X3),X4) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X3),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,X3),X4) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(resolution,[],[f3088,f96])).
% 5.81/1.13  fof(f96,plain,(
% 5.81/1.13    ( ! [X2,X3,X1] : (r2_hidden(X3,a_2_4_lattice3(X1,X2)) | ~v10_lattices(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r3_lattices(X1,X2,X3) | v2_struct_0(X1)) )),
% 5.81/1.13    inference(equality_resolution,[],[f91])).
% 5.81/1.13  fof(f91,plain,(
% 5.81/1.13    ( ! [X2,X0,X3,X1] : (v2_struct_0(X1) | ~v10_lattices(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | X0 != X3 | ~r3_lattices(X1,X2,X3) | r2_hidden(X0,a_2_4_lattice3(X1,X2))) )),
% 5.81/1.13    inference(cnf_transformation,[],[f43])).
% 5.81/1.13  fof(f43,plain,(
% 5.81/1.13    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 5.81/1.13    inference(flattening,[],[f42])).
% 5.81/1.13  fof(f42,plain,(
% 5.81/1.13    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 5.81/1.13    inference(ennf_transformation,[],[f11])).
% 5.81/1.13  fof(f11,axiom,(
% 5.81/1.13    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).
% 5.81/1.13  fof(f3088,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X1),X2)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3087,f110])).
% 5.81/1.13  fof(f3087,plain,(
% 5.81/1.13    ( ! [X2,X1] : (r1_lattices(sK0,k15_lattice3(sK0,X1),X2) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | ~v4_lattice3(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3086,f105])).
% 5.81/1.13  fof(f3086,plain,(
% 5.81/1.13    ( ! [X2,X1] : (r1_lattices(sK0,k15_lattice3(sK0,X1),X2) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | ~v10_lattices(sK0) | ~v4_lattice3(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3085,f100])).
% 5.81/1.13  fof(f3085,plain,(
% 5.81/1.13    ( ! [X2,X1] : (r1_lattices(sK0,k15_lattice3(sK0,X1),X2) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v4_lattice3(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3073,f115])).
% 5.81/1.13  fof(f3073,plain,(
% 5.81/1.13    ( ! [X2,X1] : (r1_lattices(sK0,k15_lattice3(sK0,X1),X2) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v4_lattice3(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(superposition,[],[f453,f281])).
% 5.81/1.13  fof(f281,plain,(
% 5.81/1.13    ( ! [X0] : (k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f280,f100])).
% 5.81/1.13  fof(f280,plain,(
% 5.81/1.13    ( ! [X0] : (v2_struct_0(sK0) | k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))) ) | (~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f279,f115])).
% 5.81/1.13  fof(f279,plain,(
% 5.81/1.13    ( ! [X0] : (~l3_lattices(sK0) | v2_struct_0(sK0) | k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))) ) | (~spl9_2 | ~spl9_3)),
% 5.81/1.13    inference(subsumption_resolution,[],[f278,f105])).
% 5.81/1.13  fof(f278,plain,(
% 5.81/1.13    ( ! [X0] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | k15_lattice3(sK0,X0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)))) ) | ~spl9_3),
% 5.81/1.13    inference(resolution,[],[f201,f110])).
% 5.81/1.13  fof(f201,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~v4_lattice3(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(X1) | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_4_lattice3(X1,k15_lattice3(X1,X2)))) )),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f191])).
% 5.81/1.13  fof(f191,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~v10_lattices(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1) | v2_struct_0(X1) | k15_lattice3(X1,X2) = k16_lattice3(X1,a_2_4_lattice3(X1,k15_lattice3(X1,X2))) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 5.81/1.13    inference(resolution,[],[f75,f87])).
% 5.81/1.13  fof(f75,plain,(
% 5.81/1.13    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1) )),
% 5.81/1.13    inference(cnf_transformation,[],[f33])).
% 5.81/1.13  fof(f33,plain,(
% 5.81/1.13    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.81/1.13    inference(flattening,[],[f32])).
% 5.81/1.13  fof(f32,plain,(
% 5.81/1.13    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 5.81/1.13    inference(ennf_transformation,[],[f13])).
% 5.81/1.13  fof(f13,axiom,(
% 5.81/1.13    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).
% 5.81/1.13  fof(f453,plain,(
% 5.81/1.13    ( ! [X2,X0,X1] : (r1_lattices(X0,k16_lattice3(X0,X1),X2) | ~m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0)) )),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f449])).
% 5.81/1.13  fof(f449,plain,(
% 5.81/1.13    ( ! [X2,X0,X1] : (~l3_lattices(X0) | ~m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | r1_lattices(X0,k16_lattice3(X0,X1),X2) | v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 5.81/1.13    inference(resolution,[],[f83,f94])).
% 5.81/1.13  fof(f94,plain,(
% 5.81/1.13    ( ! [X2,X0] : (r3_lattice3(X0,k16_lattice3(X0,X2),X2) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 5.81/1.13    inference(equality_resolution,[],[f80])).
% 5.81/1.13  fof(f80,plain,(
% 5.81/1.13    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) )),
% 5.81/1.13    inference(cnf_transformation,[],[f35])).
% 5.81/1.13  fof(f35,plain,(
% 5.81/1.13    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.81/1.13    inference(flattening,[],[f34])).
% 5.81/1.13  fof(f34,plain,(
% 5.81/1.13    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 5.81/1.13    inference(ennf_transformation,[],[f12])).
% 5.81/1.13  fof(f12,axiom,(
% 5.81/1.13    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 5.81/1.13  fof(f83,plain,(
% 5.81/1.13    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X0,X1,X2) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X2) | r1_lattices(X0,X1,X3) | v2_struct_0(X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f39])).
% 5.81/1.13  fof(f39,plain,(
% 5.81/1.13    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.81/1.13    inference(flattening,[],[f38])).
% 5.81/1.13  fof(f38,plain,(
% 5.81/1.13    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 5.81/1.13    inference(ennf_transformation,[],[f8])).
% 5.81/1.13  fof(f8,axiom,(
% 5.81/1.13    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 5.81/1.13  fof(f4343,plain,(
% 5.81/1.13    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f4324])).
% 5.81/1.13  fof(f4324,plain,(
% 5.81/1.13    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(resolution,[],[f3877,f333])).
% 5.81/1.13  fof(f333,plain,(
% 5.81/1.13    ( ! [X0] : (r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f332,f100])).
% 5.81/1.13  fof(f332,plain,(
% 5.81/1.13    ( ! [X0] : (r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f331,f115])).
% 5.81/1.13  fof(f331,plain,(
% 5.81/1.13    ( ! [X0] : (r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0))) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f330,f110])).
% 5.81/1.13  fof(f330,plain,(
% 5.81/1.13    ( ! [X0] : (r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0))) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f324,f105])).
% 5.81/1.13  fof(f324,plain,(
% 5.81/1.13    ( ! [X0] : (r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0))) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(superposition,[],[f94,f281])).
% 5.81/1.13  fof(f3877,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~r3_lattice3(sK0,X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r3_lattices(sK0,X2,k15_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3876,f100])).
% 5.81/1.13  fof(f3876,plain,(
% 5.81/1.13    ( ! [X2,X1] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X1)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3875,f115])).
% 5.81/1.13  fof(f3875,plain,(
% 5.81/1.13    ( ! [X2,X1] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X1)) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3874,f110])).
% 5.81/1.13  fof(f3874,plain,(
% 5.81/1.13    ( ! [X2,X1] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X1)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f3836,f105])).
% 5.81/1.13  fof(f3836,plain,(
% 5.81/1.13    ( ! [X2,X1] : (r3_lattices(sK0,X2,k15_lattice3(sK0,X1)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(superposition,[],[f95,f281])).
% 5.81/1.13  fof(f95,plain,(
% 5.81/1.13    ( ! [X2,X0,X3] : (r3_lattices(X0,X3,k16_lattice3(X0,X2)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(k16_lattice3(X0,X2),u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | v2_struct_0(X0)) )),
% 5.81/1.13    inference(equality_resolution,[],[f79])).
% 5.81/1.13  fof(f79,plain,(
% 5.81/1.13    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X3,X2) | r3_lattices(X0,X3,X1) | k16_lattice3(X0,X2) != X1) )),
% 5.81/1.13    inference(cnf_transformation,[],[f35])).
% 5.81/1.13  fof(f9659,plain,(
% 5.81/1.13    spl9_31 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_10 | ~spl9_20),
% 5.81/1.13    inference(avatar_split_clause,[],[f9636,f811,f274,f113,f108,f103,f98,f1395])).
% 5.81/1.13  fof(f1395,plain,(
% 5.81/1.13    spl9_31 <=> r3_lattices(sK0,sK2(sK0),sK2(sK0))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 5.81/1.13  fof(f9636,plain,(
% 5.81/1.13    r3_lattices(sK0,sK2(sK0),sK2(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_10 | ~spl9_20)),
% 5.81/1.13    inference(subsumption_resolution,[],[f9598,f813])).
% 5.81/1.13  fof(f9598,plain,(
% 5.81/1.13    r3_lattices(sK0,sK2(sK0),sK2(sK0)) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_10)),
% 5.81/1.13    inference(superposition,[],[f4343,f276])).
% 5.81/1.13  fof(f9525,plain,(
% 5.81/1.13    ~spl9_17 | spl9_1 | ~spl9_6 | ~spl9_25 | spl9_57),
% 5.81/1.13    inference(avatar_split_clause,[],[f9524,f2546,f1077,f125,f98,f416])).
% 5.81/1.13  fof(f1077,plain,(
% 5.81/1.13    spl9_25 <=> m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 5.81/1.13  fof(f9524,plain,(
% 5.81/1.13    ~l1_lattices(sK0) | (spl9_1 | ~spl9_6 | ~spl9_25 | spl9_57)),
% 5.81/1.13    inference(subsumption_resolution,[],[f9289,f126])).
% 5.81/1.13  fof(f9289,plain,(
% 5.81/1.13    ~l1_lattices(sK0) | ~v13_lattices(sK0) | (spl9_1 | ~spl9_25 | spl9_57)),
% 5.81/1.13    inference(subsumption_resolution,[],[f9288,f2548])).
% 5.81/1.13  fof(f2548,plain,(
% 5.81/1.13    k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | spl9_57),
% 5.81/1.13    inference(avatar_component_clause,[],[f2546])).
% 5.81/1.13  fof(f9288,plain,(
% 5.81/1.13    ~l1_lattices(sK0) | ~v13_lattices(sK0) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_25)),
% 5.81/1.13    inference(subsumption_resolution,[],[f1265,f100])).
% 5.81/1.13  fof(f1265,plain,(
% 5.81/1.13    ~l1_lattices(sK0) | ~v13_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~spl9_25),
% 5.81/1.13    inference(resolution,[],[f1079,f481])).
% 5.81/1.13  fof(f481,plain,(
% 5.81/1.13    ( ! [X2,X0] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v13_lattices(X0) | v2_struct_0(X0) | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X2)) )),
% 5.81/1.13    inference(subsumption_resolution,[],[f93,f60])).
% 5.81/1.13  fof(f93,plain,(
% 5.81/1.13    ( ! [X2,X0] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X2)) )),
% 5.81/1.13    inference(equality_resolution,[],[f62])).
% 5.81/1.13  fof(f62,plain,(
% 5.81/1.13    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_lattices(X0) | ~v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = X1 | k5_lattices(X0) != X1) )),
% 5.81/1.13    inference(cnf_transformation,[],[f27])).
% 5.81/1.13  fof(f1079,plain,(
% 5.81/1.13    m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~spl9_25),
% 5.81/1.13    inference(avatar_component_clause,[],[f1077])).
% 5.81/1.13  fof(f8838,plain,(
% 5.81/1.13    ~spl9_62 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_102),
% 5.81/1.13    inference(avatar_split_clause,[],[f8834,f4892,f125,f113,f108,f103,f98,f2784])).
% 5.81/1.13  fof(f2784,plain,(
% 5.81/1.13    spl9_62 <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).
% 5.81/1.13  fof(f4892,plain,(
% 5.81/1.13    spl9_102 <=> ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)))),
% 5.81/1.13    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).
% 5.81/1.13  fof(f8834,plain,(
% 5.81/1.13    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_102)),
% 5.81/1.13    inference(trivial_inequality_removal,[],[f8831])).
% 5.81/1.13  fof(f8831,plain,(
% 5.81/1.13    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_102)),
% 5.81/1.13    inference(superposition,[],[f4893,f8788])).
% 5.81/1.13  fof(f8788,plain,(
% 5.81/1.13    ( ! [X3] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X3)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.13    inference(superposition,[],[f8779,f1686])).
% 5.81/1.13  fof(f1686,plain,(
% 5.81/1.13    ( ! [X0] : (sK3(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0))))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.13    inference(subsumption_resolution,[],[f1685,f127])).
% 5.81/1.13  fof(f127,plain,(
% 5.81/1.13    ~v13_lattices(sK0) | spl9_6),
% 5.81/1.13    inference(avatar_component_clause,[],[f125])).
% 5.81/1.13  fof(f1685,plain,(
% 5.81/1.13    ( ! [X0] : (sK3(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0)))) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f1684,f105])).
% 5.81/1.13  fof(f1684,plain,(
% 5.81/1.13    ( ! [X0] : (sK3(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0)))) | ~v10_lattices(sK0) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f1683,f100])).
% 5.81/1.13  fof(f1683,plain,(
% 5.81/1.13    ( ! [X0] : (v2_struct_0(sK0) | sK3(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0)))) | ~v10_lattices(sK0) | v13_lattices(sK0)) ) | (~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f1682,f115])).
% 5.81/1.13  fof(f1682,plain,(
% 5.81/1.13    ( ! [X0] : (~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,k15_lattice3(sK0,X0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0)))) | ~v10_lattices(sK0) | v13_lattices(sK0)) ) | ~spl9_3),
% 5.81/1.13    inference(resolution,[],[f1026,f110])).
% 5.81/1.13  fof(f1026,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~v4_lattice3(X1) | ~l3_lattices(X1) | v2_struct_0(X1) | sK3(X1,k15_lattice3(X1,X2)) = k15_lattice3(X1,a_2_3_lattice3(X1,sK3(X1,k15_lattice3(X1,X2)))) | ~v10_lattices(X1) | v13_lattices(X1)) )),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f1010])).
% 5.81/1.13  fof(f1010,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~v4_lattice3(X1) | ~l3_lattices(X1) | v2_struct_0(X1) | sK3(X1,k15_lattice3(X1,X2)) = k15_lattice3(X1,a_2_3_lattice3(X1,sK3(X1,k15_lattice3(X1,X2)))) | ~v10_lattices(X1) | v13_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 5.81/1.13    inference(resolution,[],[f169,f87])).
% 5.81/1.13  fof(f169,plain,(
% 5.81/1.13    ( ! [X4,X5] : (~m1_subset_1(X5,u1_struct_0(X4)) | ~v4_lattice3(X4) | ~l3_lattices(X4) | v2_struct_0(X4) | sK3(X4,X5) = k15_lattice3(X4,a_2_3_lattice3(X4,sK3(X4,X5))) | ~v10_lattices(X4) | v13_lattices(X4)) )),
% 5.81/1.13    inference(subsumption_resolution,[],[f163,f50])).
% 5.81/1.13  fof(f163,plain,(
% 5.81/1.13    ( ! [X4,X5] : (~v10_lattices(X4) | ~v4_lattice3(X4) | ~l3_lattices(X4) | v2_struct_0(X4) | sK3(X4,X5) = k15_lattice3(X4,a_2_3_lattice3(X4,sK3(X4,X5))) | ~l1_lattices(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | v13_lattices(X4)) )),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f158])).
% 5.81/1.13  fof(f158,plain,(
% 5.81/1.13    ( ! [X4,X5] : (~v10_lattices(X4) | ~v4_lattice3(X4) | ~l3_lattices(X4) | v2_struct_0(X4) | sK3(X4,X5) = k15_lattice3(X4,a_2_3_lattice3(X4,sK3(X4,X5))) | ~l1_lattices(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | v2_struct_0(X4) | v13_lattices(X4)) )),
% 5.81/1.13    inference(resolution,[],[f74,f68])).
% 5.81/1.13  fof(f68,plain,(
% 5.81/1.13    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v13_lattices(X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f29])).
% 5.81/1.13  fof(f74,plain,(
% 5.81/1.13    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) )),
% 5.81/1.13    inference(cnf_transformation,[],[f33])).
% 5.81/1.13  fof(f8779,plain,(
% 5.81/1.13    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(resolution,[],[f8771,f49])).
% 5.81/1.13  fof(f49,plain,(
% 5.81/1.13    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f1])).
% 5.81/1.13  fof(f1,axiom,(
% 5.81/1.13    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 5.81/1.13  fof(f8771,plain,(
% 5.81/1.13    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f8770,f100])).
% 5.81/1.13  fof(f8770,plain,(
% 5.81/1.13    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~r1_tarski(X0,X1) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f8760,f115])).
% 5.81/1.13  fof(f8760,plain,(
% 5.81/1.13    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~r1_tarski(X0,X1) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(resolution,[],[f8750,f87])).
% 5.81/1.13  fof(f8750,plain,(
% 5.81/1.13    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~r1_tarski(X0,X1)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f8749,f100])).
% 5.81/1.13  fof(f8749,plain,(
% 5.81/1.13    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~r1_tarski(X0,X1) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f8739,f115])).
% 5.81/1.13  fof(f8739,plain,(
% 5.81/1.13    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~r1_tarski(X0,X1) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(resolution,[],[f7971,f87])).
% 5.81/1.13  fof(f7971,plain,(
% 5.81/1.13    ( ! [X6,X7] : (~m1_subset_1(k15_lattice3(sK0,X7),u1_struct_0(sK0)) | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | ~m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0)) | ~r1_tarski(X6,X7)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7970,f100])).
% 5.81/1.13  fof(f7970,plain,(
% 5.81/1.13    ( ! [X6,X7] : (~m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | ~m1_subset_1(k15_lattice3(sK0,X7),u1_struct_0(sK0)) | ~r1_tarski(X6,X7) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7969,f115])).
% 5.81/1.13  fof(f7969,plain,(
% 5.81/1.13    ( ! [X6,X7] : (~m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | ~m1_subset_1(k15_lattice3(sK0,X7),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~r1_tarski(X6,X7) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7968,f110])).
% 5.81/1.13  fof(f7968,plain,(
% 5.81/1.13    ( ! [X6,X7] : (~m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | ~m1_subset_1(k15_lattice3(sK0,X7),u1_struct_0(sK0)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X6,X7) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7940,f105])).
% 5.81/1.13  fof(f7940,plain,(
% 5.81/1.13    ( ! [X6,X7] : (~m1_subset_1(k15_lattice3(sK0,X6),u1_struct_0(sK0)) | k15_lattice3(sK0,X6) = k2_lattices(sK0,k15_lattice3(sK0,X6),k15_lattice3(sK0,X7)) | ~m1_subset_1(k15_lattice3(sK0,X7),u1_struct_0(sK0)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X6,X7) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(resolution,[],[f7918,f81])).
% 5.81/1.13  fof(f81,plain,(
% 5.81/1.13    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~r1_tarski(X1,X2) | v2_struct_0(X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f37])).
% 5.81/1.13  fof(f37,plain,(
% 5.81/1.13    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.81/1.13    inference(flattening,[],[f36])).
% 5.81/1.13  fof(f36,plain,(
% 5.81/1.13    ! [X0] : (! [X1,X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))) | ~r1_tarski(X1,X2)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 5.81/1.13    inference(ennf_transformation,[],[f14])).
% 5.81/1.13  fof(f14,axiom,(
% 5.81/1.13    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (r1_tarski(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) & r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)))))),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_lattice3)).
% 5.81/1.13  fof(f7918,plain,(
% 5.81/1.13    ( ! [X0,X1] : (~r3_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7917,f100])).
% 5.81/1.13  fof(f7917,plain,(
% 5.81/1.13    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~r3_lattices(sK0,k15_lattice3(sK0,X1),X0) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7916,f115])).
% 5.81/1.13  fof(f7916,plain,(
% 5.81/1.13    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~l3_lattices(sK0) | ~r3_lattices(sK0,k15_lattice3(sK0,X1),X0) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7915,f110])).
% 5.81/1.13  fof(f7915,plain,(
% 5.81/1.13    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r3_lattices(sK0,k15_lattice3(sK0,X1),X0) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7914,f105])).
% 5.81/1.13  fof(f7914,plain,(
% 5.81/1.13    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r3_lattices(sK0,k15_lattice3(sK0,X1),X0) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f7899])).
% 5.81/1.13  fof(f7899,plain,(
% 5.81/1.13    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X0) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,X1),X0) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(resolution,[],[f7734,f96])).
% 5.81/1.13  fof(f7734,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X2)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7733,f110])).
% 5.81/1.13  fof(f7733,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | ~v4_lattice3(sK0) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X2)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7732,f105])).
% 5.81/1.13  fof(f7732,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X2)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7731,f100])).
% 5.81/1.13  fof(f7731,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X2)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(subsumption_resolution,[],[f7717,f115])).
% 5.81/1.13  fof(f7717,plain,(
% 5.81/1.13    ( ! [X2,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_4_lattice3(sK0,k15_lattice3(sK0,X1))) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | k15_lattice3(sK0,X1) = k2_lattices(sK0,k15_lattice3(sK0,X1),X2)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.13    inference(superposition,[],[f3084,f281])).
% 5.81/1.13  fof(f3084,plain,(
% 5.81/1.13    ( ! [X4,X5,X3] : (~m1_subset_1(k16_lattice3(X3,X4),u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~l3_lattices(X3) | v2_struct_0(X3) | ~v10_lattices(X3) | ~v4_lattice3(X3) | k16_lattice3(X3,X4) = k2_lattices(X3,k16_lattice3(X3,X4),X5)) )),
% 5.81/1.13    inference(subsumption_resolution,[],[f3083,f56])).
% 5.81/1.13  fof(f56,plain,(
% 5.81/1.13    ( ! [X0] : (v8_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f21])).
% 5.81/1.13  fof(f21,plain,(
% 5.81/1.13    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 5.81/1.13    inference(flattening,[],[f20])).
% 5.81/1.13  fof(f20,plain,(
% 5.81/1.13    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 5.81/1.13    inference(ennf_transformation,[],[f2])).
% 5.81/1.13  fof(f2,axiom,(
% 5.81/1.13    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 5.81/1.13    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 5.81/1.13  fof(f3083,plain,(
% 5.81/1.13    ( ! [X4,X5,X3] : (~m1_subset_1(k16_lattice3(X3,X4),u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~l3_lattices(X3) | v2_struct_0(X3) | ~v10_lattices(X3) | ~v4_lattice3(X3) | ~v8_lattices(X3) | k16_lattice3(X3,X4) = k2_lattices(X3,k16_lattice3(X3,X4),X5)) )),
% 5.81/1.13    inference(subsumption_resolution,[],[f3080,f57])).
% 5.81/1.13  fof(f57,plain,(
% 5.81/1.13    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f21])).
% 5.81/1.13  fof(f3080,plain,(
% 5.81/1.13    ( ! [X4,X5,X3] : (~m1_subset_1(k16_lattice3(X3,X4),u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~l3_lattices(X3) | v2_struct_0(X3) | ~v10_lattices(X3) | ~v4_lattice3(X3) | ~v8_lattices(X3) | ~v9_lattices(X3) | k16_lattice3(X3,X4) = k2_lattices(X3,k16_lattice3(X3,X4),X5)) )),
% 5.81/1.13    inference(duplicate_literal_removal,[],[f3071])).
% 5.81/1.13  fof(f3071,plain,(
% 5.81/1.13    ( ! [X4,X5,X3] : (~m1_subset_1(k16_lattice3(X3,X4),u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r2_hidden(X5,X4) | ~l3_lattices(X3) | v2_struct_0(X3) | ~v10_lattices(X3) | ~v4_lattice3(X3) | ~v8_lattices(X3) | ~v9_lattices(X3) | ~l3_lattices(X3) | ~m1_subset_1(k16_lattice3(X3,X4),u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | k16_lattice3(X3,X4) = k2_lattices(X3,k16_lattice3(X3,X4),X5) | v2_struct_0(X3)) )),
% 5.81/1.13    inference(resolution,[],[f453,f59])).
% 5.81/1.13  fof(f59,plain,(
% 5.81/1.13    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) = X1 | v2_struct_0(X0)) )),
% 5.81/1.13    inference(cnf_transformation,[],[f23])).
% 5.81/1.13  fof(f23,plain,(
% 5.81/1.13    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 5.81/1.13    inference(flattening,[],[f22])).
% 5.81/1.13  fof(f22,plain,(
% 5.81/1.13    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 5.81/1.13    inference(ennf_transformation,[],[f6])).
% 5.81/1.15  fof(f6,axiom,(
% 5.81/1.15    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 5.81/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 5.81/1.15  fof(f4893,plain,(
% 5.81/1.15    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | ~spl9_102),
% 5.81/1.15    inference(avatar_component_clause,[],[f4892])).
% 5.81/1.15  fof(f8801,plain,(
% 5.81/1.15    spl9_137 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7),
% 5.81/1.15    inference(avatar_split_clause,[],[f8780,f175,f113,f108,f103,f98,f8798])).
% 5.81/1.15  fof(f175,plain,(
% 5.81/1.15    spl9_7 <=> k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 5.81/1.15  fof(f8780,plain,(
% 5.81/1.15    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7)),
% 5.81/1.15    inference(superposition,[],[f8779,f177])).
% 5.81/1.15  fof(f177,plain,(
% 5.81/1.15    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~spl9_7),
% 5.81/1.15    inference(avatar_component_clause,[],[f175])).
% 5.81/1.15  fof(f7932,plain,(
% 5.81/1.15    spl9_136 | ~spl9_62 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42 | ~spl9_122),
% 5.81/1.15    inference(avatar_split_clause,[],[f7921,f6330,f1826,f113,f108,f103,f98,f2784,f7929])).
% 5.81/1.15  fof(f7929,plain,(
% 5.81/1.15    spl9_136 <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).
% 5.81/1.15  fof(f1826,plain,(
% 5.81/1.15    spl9_42 <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 5.81/1.15  fof(f6330,plain,(
% 5.81/1.15    spl9_122 <=> r2_hidden(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).
% 5.81/1.15  fof(f7921,plain,(
% 5.81/1.15    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42 | ~spl9_122)),
% 5.81/1.15    inference(subsumption_resolution,[],[f7903,f1828])).
% 5.81/1.15  fof(f1828,plain,(
% 5.81/1.15    m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | ~spl9_42),
% 5.81/1.15    inference(avatar_component_clause,[],[f1826])).
% 5.81/1.15  fof(f7903,plain,(
% 5.81/1.15    ~m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_122)),
% 5.81/1.15    inference(resolution,[],[f7734,f6331])).
% 5.81/1.15  fof(f6331,plain,(
% 5.81/1.15    r2_hidden(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~spl9_122),
% 5.81/1.15    inference(avatar_component_clause,[],[f6330])).
% 5.81/1.15  fof(f7518,plain,(
% 5.81/1.15    ~spl9_134 | spl9_135 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11 | ~spl9_37 | ~spl9_38),
% 5.81/1.15    inference(avatar_split_clause,[],[f3977,f1525,f1487,f335,f183,f113,f108,f103,f98,f7515,f7511])).
% 5.81/1.15  fof(f7511,plain,(
% 5.81/1.15    spl9_134 <=> r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).
% 5.81/1.15  fof(f7515,plain,(
% 5.81/1.15    spl9_135 <=> r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_135])])).
% 5.81/1.15  fof(f183,plain,(
% 5.81/1.15    spl9_8 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 5.81/1.15  fof(f335,plain,(
% 5.81/1.15    spl9_11 <=> r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 5.81/1.15  fof(f1487,plain,(
% 5.81/1.15    spl9_37 <=> m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 5.81/1.15  fof(f1525,plain,(
% 5.81/1.15    spl9_38 <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 5.81/1.15  fof(f3977,plain,(
% 5.81/1.15    r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11 | ~spl9_37 | ~spl9_38)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3968,f1489])).
% 5.81/1.15  fof(f1489,plain,(
% 5.81/1.15    m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | ~spl9_37),
% 5.81/1.15    inference(avatar_component_clause,[],[f1487])).
% 5.81/1.15  fof(f3968,plain,(
% 5.81/1.15    r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11 | ~spl9_38)),
% 5.81/1.15    inference(superposition,[],[f3853,f1527])).
% 5.81/1.15  fof(f1527,plain,(
% 5.81/1.15    sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~spl9_38),
% 5.81/1.15    inference(avatar_component_clause,[],[f1525])).
% 5.81/1.15  fof(f3853,plain,(
% 5.81/1.15    ( ! [X0] : (r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) | ~r3_lattice3(sK0,k5_lattices(sK0),X0) | ~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3852,f100])).
% 5.81/1.15  fof(f3852,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3851,f185])).
% 5.81/1.15  fof(f185,plain,(
% 5.81/1.15    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl9_8),
% 5.81/1.15    inference(avatar_component_clause,[],[f183])).
% 5.81/1.15  fof(f3851,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3850,f115])).
% 5.81/1.15  fof(f3850,plain,(
% 5.81/1.15    ( ! [X0] : (~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3849,f110])).
% 5.81/1.15  fof(f3849,plain,(
% 5.81/1.15    ( ! [X0] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3848,f105])).
% 5.81/1.15  fof(f3848,plain,(
% 5.81/1.15    ( ! [X0] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f3829])).
% 5.81/1.15  fof(f3829,plain,(
% 5.81/1.15    ( ! [X0] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | ~m1_subset_1(k16_lattice3(sK0,X0),u1_struct_0(sK0)) | r1_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(resolution,[],[f95,f602])).
% 5.81/1.15  fof(f602,plain,(
% 5.81/1.15    ( ! [X0] : (~r3_lattices(sK0,k5_lattices(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k5_lattices(sK0),X0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f601,f100])).
% 5.81/1.15  fof(f601,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | r1_lattices(sK0,k5_lattices(sK0),X0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f600,f185])).
% 5.81/1.15  fof(f600,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | r1_lattices(sK0,k5_lattices(sK0),X0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f599,f115])).
% 5.81/1.15  fof(f599,plain,(
% 5.81/1.15    ( ! [X0] : (~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | r1_lattices(sK0,k5_lattices(sK0),X0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f598,f110])).
% 5.81/1.15  fof(f598,plain,(
% 5.81/1.15    ( ! [X0] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | r1_lattices(sK0,k5_lattices(sK0),X0)) ) | (spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f597,f105])).
% 5.81/1.15  fof(f597,plain,(
% 5.81/1.15    ( ! [X0] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | r1_lattices(sK0,k5_lattices(sK0),X0)) ) | (spl9_1 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f594])).
% 5.81/1.15  fof(f594,plain,(
% 5.81/1.15    ( ! [X0] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattices(sK0,k5_lattices(sK0),X0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,k5_lattices(sK0),X0)) ) | (spl9_1 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(resolution,[],[f96,f456])).
% 5.81/1.15  fof(f456,plain,(
% 5.81/1.15    ( ! [X3] : (~r2_hidden(X3,a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,k5_lattices(sK0),X3)) ) | (spl9_1 | ~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f455,f100])).
% 5.81/1.15  fof(f455,plain,(
% 5.81/1.15    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_4_lattice3(sK0,k5_lattices(sK0))) | r1_lattices(sK0,k5_lattices(sK0),X3) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_8 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f454,f185])).
% 5.81/1.15  fof(f454,plain,(
% 5.81/1.15    ( ! [X3] : (~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_4_lattice3(sK0,k5_lattices(sK0))) | r1_lattices(sK0,k5_lattices(sK0),X3) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_11)),
% 5.81/1.15    inference(subsumption_resolution,[],[f450,f115])).
% 5.81/1.15  fof(f450,plain,(
% 5.81/1.15    ( ! [X3] : (~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_4_lattice3(sK0,k5_lattices(sK0))) | r1_lattices(sK0,k5_lattices(sK0),X3) | v2_struct_0(sK0)) ) | ~spl9_11),
% 5.81/1.15    inference(resolution,[],[f83,f337])).
% 5.81/1.15  fof(f337,plain,(
% 5.81/1.15    r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~spl9_11),
% 5.81/1.15    inference(avatar_component_clause,[],[f335])).
% 5.81/1.15  fof(f7432,plain,(
% 5.81/1.15    ~spl9_62 | spl9_133 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42 | ~spl9_121),
% 5.81/1.15    inference(avatar_split_clause,[],[f7402,f6326,f1826,f113,f108,f103,f98,f7429,f2784])).
% 5.81/1.15  fof(f7429,plain,(
% 5.81/1.15    spl9_133 <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_133])])).
% 5.81/1.15  fof(f6326,plain,(
% 5.81/1.15    spl9_121 <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).
% 5.81/1.15  fof(f7402,plain,(
% 5.81/1.15    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42 | ~spl9_121)),
% 5.81/1.15    inference(subsumption_resolution,[],[f7400,f1828])).
% 5.81/1.15  fof(f7400,plain,(
% 5.81/1.15    ~m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_121)),
% 5.81/1.15    inference(resolution,[],[f6328,f3280])).
% 5.81/1.15  fof(f6328,plain,(
% 5.81/1.15    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~spl9_121),
% 5.81/1.15    inference(avatar_component_clause,[],[f6326])).
% 5.81/1.15  fof(f7393,plain,(
% 5.81/1.15    spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_64 | spl9_121),
% 5.81/1.15    inference(avatar_contradiction_clause,[],[f7392])).
% 5.81/1.15  fof(f7392,plain,(
% 5.81/1.15    $false | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_64 | spl9_121)),
% 5.81/1.15    inference(subsumption_resolution,[],[f7380,f49])).
% 5.81/1.15  fof(f7380,plain,(
% 5.81/1.15    ~r1_tarski(k1_xboole_0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_64 | spl9_121)),
% 5.81/1.15    inference(resolution,[],[f2930,f6327])).
% 5.81/1.15  fof(f6327,plain,(
% 5.81/1.15    ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | spl9_121),
% 5.81/1.15    inference(avatar_component_clause,[],[f6326])).
% 5.81/1.15  fof(f2930,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~r1_tarski(X0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_64)),
% 5.81/1.15    inference(superposition,[],[f264,f2923])).
% 5.81/1.15  fof(f2923,plain,(
% 5.81/1.15    sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | ~spl9_64),
% 5.81/1.15    inference(avatar_component_clause,[],[f2921])).
% 5.81/1.15  fof(f2921,plain,(
% 5.81/1.15    spl9_64 <=> sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).
% 5.81/1.15  fof(f264,plain,(
% 5.81/1.15    ( ! [X2,X3] : (r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X2)) | ~r1_tarski(X3,a_2_3_lattice3(sK0,k15_lattice3(sK0,X2)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f263,f100])).
% 5.81/1.15  fof(f263,plain,(
% 5.81/1.15    ( ! [X2,X3] : (r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X2)) | ~r1_tarski(X3,a_2_3_lattice3(sK0,k15_lattice3(sK0,X2))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f262,f115])).
% 5.81/1.15  fof(f262,plain,(
% 5.81/1.15    ( ! [X2,X3] : (r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X2)) | ~l3_lattices(sK0) | ~r1_tarski(X3,a_2_3_lattice3(sK0,k15_lattice3(sK0,X2))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f261,f110])).
% 5.81/1.15  fof(f261,plain,(
% 5.81/1.15    ( ! [X2,X3] : (r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X2)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X3,a_2_3_lattice3(sK0,k15_lattice3(sK0,X2))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f258,f105])).
% 5.81/1.15  fof(f258,plain,(
% 5.81/1.15    ( ! [X2,X3] : (r3_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X2)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X3,a_2_3_lattice3(sK0,k15_lattice3(sK0,X2))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(superposition,[],[f81,f253])).
% 5.81/1.15  fof(f253,plain,(
% 5.81/1.15    ( ! [X0] : (k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k15_lattice3(sK0,X0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f252,f100])).
% 5.81/1.15  fof(f252,plain,(
% 5.81/1.15    ( ! [X0] : (v2_struct_0(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k15_lattice3(sK0,X0)))) ) | (~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f251,f115])).
% 5.81/1.15  fof(f251,plain,(
% 5.81/1.15    ( ! [X0] : (~l3_lattices(sK0) | v2_struct_0(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k15_lattice3(sK0,X0)))) ) | (~spl9_2 | ~spl9_3)),
% 5.81/1.15    inference(subsumption_resolution,[],[f250,f105])).
% 5.81/1.15  fof(f250,plain,(
% 5.81/1.15    ( ! [X0] : (~v10_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | k15_lattice3(sK0,X0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k15_lattice3(sK0,X0)))) ) | ~spl9_3),
% 5.81/1.15    inference(resolution,[],[f165,f110])).
% 5.81/1.15  fof(f165,plain,(
% 5.81/1.15    ( ! [X2,X1] : (~v4_lattice3(X1) | ~v10_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(X1) | k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_3_lattice3(X1,k15_lattice3(X1,X2)))) )),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f156])).
% 5.81/1.15  fof(f156,plain,(
% 5.81/1.15    ( ! [X2,X1] : (~v10_lattices(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1) | v2_struct_0(X1) | k15_lattice3(X1,X2) = k15_lattice3(X1,a_2_3_lattice3(X1,k15_lattice3(X1,X2))) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 5.81/1.15    inference(resolution,[],[f74,f87])).
% 5.81/1.15  fof(f7279,plain,(
% 5.81/1.15    spl9_132 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_43),
% 5.81/1.15    inference(avatar_split_clause,[],[f1956,f1924,f113,f108,f103,f98,f7276])).
% 5.81/1.15  fof(f7276,plain,(
% 5.81/1.15    spl9_132 <=> sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_132])])).
% 5.81/1.15  fof(f1924,plain,(
% 5.81/1.15    spl9_43 <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),u1_struct_0(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 5.81/1.15  fof(f1956,plain,(
% 5.81/1.15    sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_43)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1955,f100])).
% 5.81/1.15  fof(f1955,plain,(
% 5.81/1.15    v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_43)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1954,f115])).
% 5.81/1.15  fof(f1954,plain,(
% 5.81/1.15    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) | (~spl9_2 | ~spl9_3 | ~spl9_43)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1953,f110])).
% 5.81/1.15  fof(f1953,plain,(
% 5.81/1.15    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) | (~spl9_2 | ~spl9_43)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1935,f105])).
% 5.81/1.15  fof(f1935,plain,(
% 5.81/1.15    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) | ~spl9_43),
% 5.81/1.15    inference(resolution,[],[f1926,f75])).
% 5.81/1.15  fof(f1926,plain,(
% 5.81/1.15    m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),u1_struct_0(sK0)) | ~spl9_43),
% 5.81/1.15    inference(avatar_component_clause,[],[f1924])).
% 5.81/1.15  fof(f7098,plain,(
% 5.81/1.15    spl9_131 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_43),
% 5.81/1.15    inference(avatar_split_clause,[],[f1952,f1924,f113,f108,f103,f98,f7095])).
% 5.81/1.15  fof(f7095,plain,(
% 5.81/1.15    spl9_131 <=> sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).
% 5.81/1.15  fof(f1952,plain,(
% 5.81/1.15    sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_43)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1951,f100])).
% 5.81/1.15  fof(f1951,plain,(
% 5.81/1.15    v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_43)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1950,f115])).
% 5.81/1.15  fof(f1950,plain,(
% 5.81/1.15    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) | (~spl9_2 | ~spl9_3 | ~spl9_43)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1949,f110])).
% 5.81/1.15  fof(f1949,plain,(
% 5.81/1.15    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) | (~spl9_2 | ~spl9_43)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1934,f105])).
% 5.81/1.15  fof(f1934,plain,(
% 5.81/1.15    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) | ~spl9_43),
% 5.81/1.15    inference(resolution,[],[f1926,f74])).
% 5.81/1.15  fof(f7056,plain,(
% 5.81/1.15    spl9_129 | ~spl9_130 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_36 | ~spl9_37),
% 5.81/1.15    inference(avatar_split_clause,[],[f6804,f1487,f1442,f211,f183,f113,f108,f103,f98,f7053,f7049])).
% 5.81/1.15  fof(f7049,plain,(
% 5.81/1.15    spl9_129 <=> r1_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_129])])).
% 5.81/1.15  fof(f7053,plain,(
% 5.81/1.15    spl9_130 <=> r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).
% 5.81/1.15  fof(f211,plain,(
% 5.81/1.15    spl9_9 <=> k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 5.81/1.15  fof(f1442,plain,(
% 5.81/1.15    spl9_36 <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 5.81/1.15  fof(f6804,plain,(
% 5.81/1.15    ~r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k5_lattices(sK0))) | r1_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_36 | ~spl9_37)),
% 5.81/1.15    inference(subsumption_resolution,[],[f6784,f1489])).
% 5.81/1.15  fof(f6784,plain,(
% 5.81/1.15    ~r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_36)),
% 5.81/1.15    inference(superposition,[],[f6767,f1444])).
% 5.81/1.15  fof(f1444,plain,(
% 5.81/1.15    sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~spl9_36),
% 5.81/1.15    inference(avatar_component_clause,[],[f1442])).
% 5.81/1.15  fof(f6767,plain,(
% 5.81/1.15    ( ! [X0] : (~r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(subsumption_resolution,[],[f6751,f185])).
% 5.81/1.15  fof(f6751,plain,(
% 5.81/1.15    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9)),
% 5.81/1.15    inference(superposition,[],[f3867,f213])).
% 5.81/1.15  fof(f213,plain,(
% 5.81/1.15    k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~spl9_9),
% 5.81/1.15    inference(avatar_component_clause,[],[f211])).
% 5.81/1.15  fof(f3867,plain,(
% 5.81/1.15    ( ! [X4,X5] : (r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4)) | ~m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k15_lattice3(sK0,X5),X4) | ~m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3866,f100])).
% 5.81/1.15  fof(f3866,plain,(
% 5.81/1.15    ( ! [X4,X5] : (~m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k15_lattice3(sK0,X5),X4) | v2_struct_0(sK0) | r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3865,f115])).
% 5.81/1.15  fof(f3865,plain,(
% 5.81/1.15    ( ! [X4,X5] : (~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k15_lattice3(sK0,X5),X4) | v2_struct_0(sK0) | r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3864,f110])).
% 5.81/1.15  fof(f3864,plain,(
% 5.81/1.15    ( ! [X4,X5] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k15_lattice3(sK0,X5),X4) | v2_struct_0(sK0) | r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3845,f105])).
% 5.81/1.15  fof(f3845,plain,(
% 5.81/1.15    ( ! [X4,X5] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k15_lattice3(sK0,X5),X4) | v2_struct_0(sK0) | r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f3832])).
% 5.81/1.15  fof(f3832,plain,(
% 5.81/1.15    ( ! [X4,X5] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0)) | ~r3_lattice3(sK0,k15_lattice3(sK0,X5),X4) | v2_struct_0(sK0) | ~m1_subset_1(k16_lattice3(sK0,X4),u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X5),k16_lattice3(sK0,X4)) | ~m1_subset_1(k15_lattice3(sK0,X5),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(resolution,[],[f95,f3280])).
% 5.81/1.15  fof(f7032,plain,(
% 5.81/1.15    spl9_128 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36),
% 5.81/1.15    inference(avatar_split_clause,[],[f2161,f1442,f125,f113,f108,f103,f98,f7029])).
% 5.81/1.15  fof(f7029,plain,(
% 5.81/1.15    spl9_128 <=> r3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).
% 5.81/1.15  fof(f2161,plain,(
% 5.81/1.15    r3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36)),
% 5.81/1.15    inference(superposition,[],[f2055,f1444])).
% 5.81/1.15  fof(f2055,plain,(
% 5.81/1.15    ( ! [X1] : (r3_lattice3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1)))))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(superposition,[],[f2041,f1686])).
% 5.81/1.15  fof(f2041,plain,(
% 5.81/1.15    ( ! [X10] : (r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10))))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2040,f100])).
% 5.81/1.15  fof(f2040,plain,(
% 5.81/1.15    ( ! [X10] : (r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2039,f1732])).
% 5.81/1.15  fof(f1732,plain,(
% 5.81/1.15    ( ! [X44] : (m1_subset_1(sK3(sK0,k15_lattice3(sK0,X44)),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1731,f100])).
% 5.81/1.15  fof(f1731,plain,(
% 5.81/1.15    ( ! [X44] : (m1_subset_1(sK3(sK0,k15_lattice3(sK0,X44)),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1722,f115])).
% 5.81/1.15  fof(f1722,plain,(
% 5.81/1.15    ( ! [X44] : (m1_subset_1(sK3(sK0,k15_lattice3(sK0,X44)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(superposition,[],[f87,f1686])).
% 5.81/1.15  fof(f2039,plain,(
% 5.81/1.15    ( ! [X10] : (r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)))) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X10)),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2038,f115])).
% 5.81/1.15  fof(f2038,plain,(
% 5.81/1.15    ( ! [X10] : (r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)))) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X10)),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2037,f110])).
% 5.81/1.15  fof(f2037,plain,(
% 5.81/1.15    ( ! [X10] : (r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)))) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X10)),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2034,f105])).
% 5.81/1.15  fof(f2034,plain,(
% 5.81/1.15    ( ! [X10] : (r3_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)),a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X10)))) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X10)),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(superposition,[],[f94,f1701])).
% 5.81/1.15  fof(f1701,plain,(
% 5.81/1.15    ( ! [X13] : (sK3(sK0,k15_lattice3(sK0,X13)) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X13))))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(superposition,[],[f281,f1686])).
% 5.81/1.15  fof(f7027,plain,(
% 5.81/1.15    spl9_107 | ~spl9_68 | ~spl9_69 | ~spl9_127 | spl9_1 | ~spl9_4 | ~spl9_8 | ~spl9_21 | ~spl9_25),
% 5.81/1.15    inference(avatar_split_clause,[],[f1580,f1077,f837,f183,f113,f98,f7024,f3350,f3346,f5062])).
% 5.81/1.15  fof(f5062,plain,(
% 5.81/1.15    spl9_107 <=> r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_107])])).
% 5.81/1.15  fof(f3346,plain,(
% 5.81/1.15    spl9_68 <=> v9_lattices(sK0)),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).
% 5.81/1.15  fof(f3350,plain,(
% 5.81/1.15    spl9_69 <=> v8_lattices(sK0)),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_69])])).
% 5.81/1.15  fof(f837,plain,(
% 5.81/1.15    spl9_21 <=> k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 5.81/1.15  fof(f1580,plain,(
% 5.81/1.15    sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) | (spl9_1 | ~spl9_4 | ~spl9_8 | ~spl9_21 | ~spl9_25)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1579,f100])).
% 5.81/1.15  fof(f1579,plain,(
% 5.81/1.15    sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | v2_struct_0(sK0) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) | (~spl9_4 | ~spl9_8 | ~spl9_21 | ~spl9_25)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1578,f185])).
% 5.81/1.15  fof(f1578,plain,(
% 5.81/1.15    sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) | (~spl9_4 | ~spl9_21 | ~spl9_25)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1577,f1079])).
% 5.81/1.15  fof(f1577,plain,(
% 5.81/1.15    sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) | (~spl9_4 | ~spl9_21)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1565,f115])).
% 5.81/1.15  fof(f1565,plain,(
% 5.81/1.15    sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) | ~spl9_21),
% 5.81/1.15    inference(superposition,[],[f58,f839])).
% 5.81/1.15  fof(f839,plain,(
% 5.81/1.15    k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~spl9_21),
% 5.81/1.15    inference(avatar_component_clause,[],[f837])).
% 5.81/1.15  fof(f58,plain,(
% 5.81/1.15    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) != X1 | ~v8_lattices(X0) | ~v9_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r1_lattices(X0,X1,X2)) )),
% 5.81/1.15    inference(cnf_transformation,[],[f23])).
% 5.81/1.15  fof(f6876,plain,(
% 5.81/1.15    ~spl9_17 | spl9_126 | spl9_1 | spl9_6 | ~spl9_110),
% 5.81/1.15    inference(avatar_split_clause,[],[f6137,f6106,f125,f98,f6874,f416])).
% 5.81/1.15  fof(f6874,plain,(
% 5.81/1.15    spl9_126 <=> ! [X32,X31] : (k2_lattices(sK0,sK3(sK0,X31),sK3(sK0,k15_lattice3(sK0,X32))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X32)),sK3(sK0,X31)) | ~m1_subset_1(X31,u1_struct_0(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_126])])).
% 5.81/1.15  fof(f6106,plain,(
% 5.81/1.15    spl9_110 <=> ! [X5,X6] : (~m1_subset_1(X5,u1_struct_0(sK0)) | k2_lattices(sK0,X5,sK3(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X6)),X5))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).
% 5.81/1.15  fof(f6137,plain,(
% 5.81/1.15    ( ! [X31,X32] : (k2_lattices(sK0,sK3(sK0,X31),sK3(sK0,k15_lattice3(sK0,X32))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X32)),sK3(sK0,X31)) | ~l1_lattices(sK0) | ~m1_subset_1(X31,u1_struct_0(sK0))) ) | (spl9_1 | spl9_6 | ~spl9_110)),
% 5.81/1.15    inference(subsumption_resolution,[],[f6136,f127])).
% 5.81/1.15  fof(f6136,plain,(
% 5.81/1.15    ( ! [X31,X32] : (k2_lattices(sK0,sK3(sK0,X31),sK3(sK0,k15_lattice3(sK0,X32))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X32)),sK3(sK0,X31)) | ~l1_lattices(sK0) | ~m1_subset_1(X31,u1_struct_0(sK0)) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_110)),
% 5.81/1.15    inference(subsumption_resolution,[],[f6130,f100])).
% 5.81/1.15  fof(f6130,plain,(
% 5.81/1.15    ( ! [X31,X32] : (k2_lattices(sK0,sK3(sK0,X31),sK3(sK0,k15_lattice3(sK0,X32))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X32)),sK3(sK0,X31)) | ~l1_lattices(sK0) | ~m1_subset_1(X31,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | ~spl9_110),
% 5.81/1.15    inference(resolution,[],[f6107,f68])).
% 5.81/1.15  fof(f6107,plain,(
% 5.81/1.15    ( ! [X6,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | k2_lattices(sK0,X5,sK3(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X6)),X5)) ) | ~spl9_110),
% 5.81/1.15    inference(avatar_component_clause,[],[f6106])).
% 5.81/1.15  fof(f6634,plain,(
% 5.81/1.15    spl9_125 | ~spl9_36 | ~spl9_98),
% 5.81/1.15    inference(avatar_split_clause,[],[f4248,f4242,f1442,f6631])).
% 5.81/1.15  fof(f6631,plain,(
% 5.81/1.15    spl9_125 <=> sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_125])])).
% 5.81/1.15  fof(f4242,plain,(
% 5.81/1.15    spl9_98 <=> ! [X0] : sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).
% 5.81/1.15  fof(f4248,plain,(
% 5.81/1.15    sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (~spl9_36 | ~spl9_98)),
% 5.81/1.15    inference(superposition,[],[f4243,f1444])).
% 5.81/1.15  fof(f4243,plain,(
% 5.81/1.15    ( ! [X0] : (sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))) ) | ~spl9_98),
% 5.81/1.15    inference(avatar_component_clause,[],[f4242])).
% 5.81/1.15  fof(f6453,plain,(
% 5.81/1.15    spl9_124 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36),
% 5.81/1.15    inference(avatar_split_clause,[],[f2512,f1442,f125,f113,f108,f103,f98,f6450])).
% 5.81/1.15  fof(f6450,plain,(
% 5.81/1.15    spl9_124 <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))))),u1_struct_0(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).
% 5.81/1.15  fof(f2512,plain,(
% 5.81/1.15    m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))))),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36)),
% 5.81/1.15    inference(superposition,[],[f2304,f1444])).
% 5.81/1.15  fof(f2304,plain,(
% 5.81/1.15    ( ! [X46] : (m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X46)))))))),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(superposition,[],[f1995,f1691])).
% 5.81/1.15  fof(f1691,plain,(
% 5.81/1.15    ( ! [X1] : (sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1)))))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(superposition,[],[f1686,f1686])).
% 5.81/1.15  fof(f1995,plain,(
% 5.81/1.15    ( ! [X1] : (m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1)))))),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(superposition,[],[f1897,f1686])).
% 5.81/1.15  fof(f1897,plain,(
% 5.81/1.15    ( ! [X1] : (m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1))))),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(superposition,[],[f1799,f1686])).
% 5.81/1.15  fof(f1799,plain,(
% 5.81/1.15    ( ! [X1] : (m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1)))),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(superposition,[],[f1756,f1686])).
% 5.81/1.15  fof(f1756,plain,(
% 5.81/1.15    ( ! [X1] : (m1_subset_1(sK3(sK0,sK3(sK0,k15_lattice3(sK0,X1))),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(superposition,[],[f1732,f1686])).
% 5.81/1.15  fof(f6433,plain,(
% 5.81/1.15    spl9_123 | ~spl9_62 | ~spl9_68 | ~spl9_69 | spl9_1 | ~spl9_4 | ~spl9_37 | ~spl9_77),
% 5.81/1.15    inference(avatar_split_clause,[],[f3600,f3593,f1487,f113,f98,f3350,f3346,f2784,f6430])).
% 5.81/1.15  fof(f6430,plain,(
% 5.81/1.15    spl9_123 <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_123])])).
% 5.81/1.15  fof(f3593,plain,(
% 5.81/1.15    spl9_77 <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_77])])).
% 5.81/1.15  fof(f3600,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_4 | ~spl9_37 | ~spl9_77)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3599,f100])).
% 5.81/1.15  fof(f3599,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_37 | ~spl9_77)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3598,f1489])).
% 5.81/1.15  fof(f3598,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_77)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3597,f115])).
% 5.81/1.15  fof(f3597,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0) | ~spl9_77),
% 5.81/1.15    inference(resolution,[],[f3595,f59])).
% 5.81/1.15  fof(f3595,plain,(
% 5.81/1.15    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~spl9_77),
% 5.81/1.15    inference(avatar_component_clause,[],[f3593])).
% 5.81/1.15  fof(f6340,plain,(
% 5.81/1.15    ~spl9_121 | ~spl9_62 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42 | spl9_122),
% 5.81/1.15    inference(avatar_split_clause,[],[f6339,f6330,f1826,f113,f108,f103,f98,f2784,f6326])).
% 5.81/1.15  fof(f6339,plain,(
% 5.81/1.15    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42 | spl9_122)),
% 5.81/1.15    inference(subsumption_resolution,[],[f6338,f100])).
% 5.81/1.15  fof(f6338,plain,(
% 5.81/1.15    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42 | spl9_122)),
% 5.81/1.15    inference(subsumption_resolution,[],[f6337,f1828])).
% 5.81/1.15  fof(f6337,plain,(
% 5.81/1.15    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_122)),
% 5.81/1.15    inference(subsumption_resolution,[],[f6336,f115])).
% 5.81/1.15  fof(f6336,plain,(
% 5.81/1.15    ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | spl9_122)),
% 5.81/1.15    inference(subsumption_resolution,[],[f6335,f110])).
% 5.81/1.15  fof(f6335,plain,(
% 5.81/1.15    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | v2_struct_0(sK0) | (~spl9_2 | spl9_122)),
% 5.81/1.15    inference(subsumption_resolution,[],[f6334,f105])).
% 5.81/1.15  fof(f6334,plain,(
% 5.81/1.15    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | v2_struct_0(sK0) | spl9_122),
% 5.81/1.15    inference(resolution,[],[f6332,f96])).
% 5.81/1.15  fof(f6332,plain,(
% 5.81/1.15    ~r2_hidden(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | spl9_122),
% 5.81/1.15    inference(avatar_component_clause,[],[f6330])).
% 5.81/1.15  fof(f6333,plain,(
% 5.81/1.15    spl9_121 | ~spl9_122 | ~spl9_64 | ~spl9_71),
% 5.81/1.15    inference(avatar_split_clause,[],[f3531,f3522,f2921,f6330,f6326])).
% 5.81/1.15  fof(f3522,plain,(
% 5.81/1.15    spl9_71 <=> ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).
% 5.81/1.15  fof(f3531,plain,(
% 5.81/1.15    ~r2_hidden(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (~spl9_64 | ~spl9_71)),
% 5.81/1.15    inference(superposition,[],[f3523,f2923])).
% 5.81/1.15  fof(f3523,plain,(
% 5.81/1.15    ( ! [X0] : (~r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | ~spl9_71),
% 5.81/1.15    inference(avatar_component_clause,[],[f3522])).
% 5.81/1.15  fof(f6303,plain,(
% 5.81/1.15    spl9_119 | ~spl9_120 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23 | ~spl9_36),
% 5.81/1.15    inference(avatar_split_clause,[],[f1470,f1442,f981,f113,f108,f103,f98,f6300,f6296])).
% 5.81/1.15  fof(f6296,plain,(
% 5.81/1.15    spl9_119 <=> r3_lattices(sK0,sK2(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_119])])).
% 5.81/1.15  fof(f6300,plain,(
% 5.81/1.15    spl9_120 <=> r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,sK2(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).
% 5.81/1.15  fof(f981,plain,(
% 5.81/1.15    spl9_23 <=> sK2(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK2(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 5.81/1.15  fof(f1470,plain,(
% 5.81/1.15    ~r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,sK2(sK0))) | r3_lattices(sK0,sK2(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23 | ~spl9_36)),
% 5.81/1.15    inference(superposition,[],[f1220,f1444])).
% 5.81/1.15  fof(f1220,plain,(
% 5.81/1.15    ( ! [X1] : (~r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X1)),a_2_4_lattice3(sK0,sK2(sK0))) | r3_lattices(sK0,sK2(sK0),k15_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23)),
% 5.81/1.15    inference(superposition,[],[f291,f983])).
% 5.81/1.15  fof(f983,plain,(
% 5.81/1.15    sK2(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK2(sK0))) | ~spl9_23),
% 5.81/1.15    inference(avatar_component_clause,[],[f981])).
% 5.81/1.15  fof(f291,plain,(
% 5.81/1.15    ( ! [X2,X3] : (r3_lattices(sK0,k16_lattice3(sK0,X3),k15_lattice3(sK0,X2)) | ~r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X2)),X3)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f290,f100])).
% 5.81/1.15  fof(f290,plain,(
% 5.81/1.15    ( ! [X2,X3] : (r3_lattices(sK0,k16_lattice3(sK0,X3),k15_lattice3(sK0,X2)) | ~r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X2)),X3) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f289,f115])).
% 5.81/1.15  fof(f289,plain,(
% 5.81/1.15    ( ! [X2,X3] : (r3_lattices(sK0,k16_lattice3(sK0,X3),k15_lattice3(sK0,X2)) | ~l3_lattices(sK0) | ~r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X2)),X3) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f288,f110])).
% 5.81/1.15  fof(f288,plain,(
% 5.81/1.15    ( ! [X2,X3] : (r3_lattices(sK0,k16_lattice3(sK0,X3),k15_lattice3(sK0,X2)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X2)),X3) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f286,f105])).
% 5.81/1.15  fof(f286,plain,(
% 5.81/1.15    ( ! [X2,X3] : (r3_lattices(sK0,k16_lattice3(sK0,X3),k15_lattice3(sK0,X2)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X2)),X3) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(superposition,[],[f82,f281])).
% 5.81/1.15  fof(f82,plain,(
% 5.81/1.15    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),k16_lattice3(X0,X1)) | ~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~r1_tarski(X1,X2) | v2_struct_0(X0)) )),
% 5.81/1.15    inference(cnf_transformation,[],[f37])).
% 5.81/1.15  fof(f6294,plain,(
% 5.81/1.15    spl9_117 | ~spl9_118 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23 | ~spl9_36),
% 5.81/1.15    inference(avatar_split_clause,[],[f1469,f1442,f981,f113,f108,f103,f98,f6291,f6287])).
% 5.81/1.15  fof(f6287,plain,(
% 5.81/1.15    spl9_117 <=> r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK2(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_117])])).
% 5.81/1.15  fof(f6291,plain,(
% 5.81/1.15    spl9_118 <=> r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_118])])).
% 5.81/1.15  fof(f1469,plain,(
% 5.81/1.15    ~r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK2(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23 | ~spl9_36)),
% 5.81/1.15    inference(superposition,[],[f1219,f1444])).
% 5.81/1.15  fof(f1219,plain,(
% 5.81/1.15    ( ! [X0] : (~r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0))) | r3_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23)),
% 5.81/1.15    inference(superposition,[],[f295,f983])).
% 5.81/1.15  fof(f295,plain,(
% 5.81/1.15    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X4),k16_lattice3(sK0,X5)) | ~r1_tarski(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,X4)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f294,f100])).
% 5.81/1.15  fof(f294,plain,(
% 5.81/1.15    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X4),k16_lattice3(sK0,X5)) | ~r1_tarski(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,X4))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f293,f115])).
% 5.81/1.15  fof(f293,plain,(
% 5.81/1.15    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X4),k16_lattice3(sK0,X5)) | ~l3_lattices(sK0) | ~r1_tarski(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,X4))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f292,f110])).
% 5.81/1.15  fof(f292,plain,(
% 5.81/1.15    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X4),k16_lattice3(sK0,X5)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,X4))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f287,f105])).
% 5.81/1.15  fof(f287,plain,(
% 5.81/1.15    ( ! [X4,X5] : (r3_lattices(sK0,k15_lattice3(sK0,X4),k16_lattice3(sK0,X5)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X5,a_2_4_lattice3(sK0,k15_lattice3(sK0,X4))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(superposition,[],[f82,f281])).
% 5.81/1.15  fof(f6285,plain,(
% 5.81/1.15    spl9_114 | ~spl9_116 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_36),
% 5.81/1.15    inference(avatar_split_clause,[],[f1463,f1442,f211,f113,f108,f103,f98,f6282,f6272])).
% 5.81/1.15  fof(f6272,plain,(
% 5.81/1.15    spl9_114 <=> r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).
% 5.81/1.15  fof(f6282,plain,(
% 5.81/1.15    spl9_116 <=> r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).
% 5.81/1.15  fof(f1463,plain,(
% 5.81/1.15    ~r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_36)),
% 5.81/1.15    inference(superposition,[],[f311,f1444])).
% 5.81/1.15  fof(f311,plain,(
% 5.81/1.15    ( ! [X0] : (~r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k15_lattice3(sK0,X0))) | r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9)),
% 5.81/1.15    inference(superposition,[],[f295,f213])).
% 5.81/1.15  fof(f6280,plain,(
% 5.81/1.15    spl9_112 | ~spl9_115 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_36),
% 5.81/1.15    inference(avatar_split_clause,[],[f1460,f1442,f211,f113,f108,f103,f98,f6277,f6263])).
% 5.81/1.15  fof(f6263,plain,(
% 5.81/1.15    spl9_112 <=> r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_112])])).
% 5.81/1.15  fof(f6277,plain,(
% 5.81/1.15    spl9_115 <=> r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_115])])).
% 5.81/1.15  fof(f1460,plain,(
% 5.81/1.15    ~r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,k5_lattices(sK0))) | r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_36)),
% 5.81/1.15    inference(superposition,[],[f305,f1444])).
% 5.81/1.15  fof(f305,plain,(
% 5.81/1.15    ( ! [X0] : (~r1_tarski(a_2_4_lattice3(sK0,k15_lattice3(sK0,X0)),a_2_4_lattice3(sK0,k5_lattices(sK0))) | r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9)),
% 5.81/1.15    inference(superposition,[],[f291,f213])).
% 5.81/1.15  fof(f6275,plain,(
% 5.81/1.15    ~spl9_113 | spl9_114 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7 | ~spl9_36),
% 5.81/1.15    inference(avatar_split_clause,[],[f1447,f1442,f175,f113,f108,f103,f98,f6272,f6268])).
% 5.81/1.15  fof(f6268,plain,(
% 5.81/1.15    spl9_113 <=> r1_tarski(a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_3_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_113])])).
% 5.81/1.15  fof(f1447,plain,(
% 5.81/1.15    r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | ~r1_tarski(a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_3_lattice3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7 | ~spl9_36)),
% 5.81/1.15    inference(superposition,[],[f225,f1444])).
% 5.81/1.15  fof(f225,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~r1_tarski(X0,a_2_3_lattice3(sK0,k5_lattices(sK0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7)),
% 5.81/1.15    inference(subsumption_resolution,[],[f224,f100])).
% 5.81/1.15  fof(f224,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~r1_tarski(X0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7)),
% 5.81/1.15    inference(subsumption_resolution,[],[f223,f115])).
% 5.81/1.15  fof(f223,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~l3_lattices(sK0) | ~r1_tarski(X0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_7)),
% 5.81/1.15    inference(subsumption_resolution,[],[f222,f110])).
% 5.81/1.15  fof(f222,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_7)),
% 5.81/1.15    inference(subsumption_resolution,[],[f217,f105])).
% 5.81/1.15  fof(f217,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | ~spl9_7),
% 5.81/1.15    inference(superposition,[],[f81,f177])).
% 5.81/1.15  fof(f6266,plain,(
% 5.81/1.15    ~spl9_111 | spl9_112 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7 | ~spl9_36),
% 5.81/1.15    inference(avatar_split_clause,[],[f1446,f1442,f175,f113,f108,f103,f98,f6263,f6259])).
% 5.81/1.15  fof(f6259,plain,(
% 5.81/1.15    spl9_111 <=> r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_111])])).
% 5.81/1.15  fof(f1446,plain,(
% 5.81/1.15    r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7 | ~spl9_36)),
% 5.81/1.15    inference(superposition,[],[f221,f1444])).
% 5.81/1.15  fof(f221,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) | ~r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),X0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7)),
% 5.81/1.15    inference(subsumption_resolution,[],[f220,f100])).
% 5.81/1.15  fof(f220,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) | ~r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),X0) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7)),
% 5.81/1.15    inference(subsumption_resolution,[],[f219,f115])).
% 5.81/1.15  fof(f219,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) | ~l3_lattices(sK0) | ~r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),X0) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_7)),
% 5.81/1.15    inference(subsumption_resolution,[],[f218,f110])).
% 5.81/1.15  fof(f218,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),X0) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_7)),
% 5.81/1.15    inference(subsumption_resolution,[],[f216,f105])).
% 5.81/1.15  fof(f216,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),X0) | v2_struct_0(sK0)) ) | ~spl9_7),
% 5.81/1.15    inference(superposition,[],[f81,f177])).
% 5.81/1.15  fof(f6108,plain,(
% 5.81/1.15    spl9_110 | ~spl9_17 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_15),
% 5.81/1.15    inference(avatar_split_clause,[],[f1758,f409,f125,f113,f108,f103,f98,f416,f6106])).
% 5.81/1.15  fof(f409,plain,(
% 5.81/1.15    spl9_15 <=> v6_lattices(sK0)),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 5.81/1.15  fof(f1758,plain,(
% 5.81/1.15    ( ! [X6,X5] : (~l1_lattices(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k2_lattices(sK0,X5,sK3(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X6)),X5)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_15)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1757,f410])).
% 5.81/1.15  fof(f410,plain,(
% 5.81/1.15    v6_lattices(sK0) | ~spl9_15),
% 5.81/1.15    inference(avatar_component_clause,[],[f409])).
% 5.81/1.15  fof(f1757,plain,(
% 5.81/1.15    ( ! [X6,X5] : (~l1_lattices(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | k2_lattices(sK0,X5,sK3(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X6)),X5) | ~v6_lattices(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1738,f100])).
% 5.81/1.15  fof(f1738,plain,(
% 5.81/1.15    ( ! [X6,X5] : (~l1_lattices(sK0) | ~m1_subset_1(X5,u1_struct_0(sK0)) | v2_struct_0(sK0) | k2_lattices(sK0,X5,sK3(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X6)),X5) | ~v6_lattices(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(resolution,[],[f1732,f72])).
% 5.81/1.15  fof(f72,plain,(
% 5.81/1.15    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~v6_lattices(X0)) )),
% 5.81/1.15    inference(cnf_transformation,[],[f31])).
% 5.81/1.15  fof(f31,plain,(
% 5.81/1.15    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.81/1.15    inference(flattening,[],[f30])).
% 5.81/1.15  fof(f30,plain,(
% 5.81/1.15    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 5.81/1.15    inference(ennf_transformation,[],[f9])).
% 5.81/1.15  fof(f9,axiom,(
% 5.81/1.15    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 5.81/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 5.81/1.15  fof(f5106,plain,(
% 5.81/1.15    spl9_109 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_64),
% 5.81/1.15    inference(avatar_split_clause,[],[f4112,f2921,f125,f113,f108,f103,f98,f5103])).
% 5.81/1.15  fof(f5103,plain,(
% 5.81/1.15    spl9_109 <=> r1_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_109])])).
% 5.81/1.15  fof(f4112,plain,(
% 5.81/1.15    r1_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_64)),
% 5.81/1.15    inference(superposition,[],[f4100,f2923])).
% 5.81/1.15  fof(f4100,plain,(
% 5.81/1.15    ( ! [X0] : (r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4090,f1732])).
% 5.81/1.15  fof(f4090,plain,(
% 5.81/1.15    ( ! [X0] : (r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(resolution,[],[f4077,f2764])).
% 5.81/1.15  fof(f2764,plain,(
% 5.81/1.15    ( ! [X4,X3] : (~r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2763,f100])).
% 5.81/1.15  fof(f2763,plain,(
% 5.81/1.15    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | ~r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2762,f1732])).
% 5.81/1.15  fof(f2762,plain,(
% 5.81/1.15    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X4)),u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2761,f115])).
% 5.81/1.15  fof(f2761,plain,(
% 5.81/1.15    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X4)),u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2760,f110])).
% 5.81/1.15  fof(f2760,plain,(
% 5.81/1.15    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X4)),u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2759,f105])).
% 5.81/1.15  fof(f2759,plain,(
% 5.81/1.15    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X4)),u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f2752])).
% 5.81/1.15  fof(f2752,plain,(
% 5.81/1.15    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X4)),u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X4)),X3) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(resolution,[],[f2058,f96])).
% 5.81/1.15  fof(f2058,plain,(
% 5.81/1.15    ( ! [X0,X1] : (~r2_hidden(X1,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0)))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),X1)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2057,f100])).
% 5.81/1.15  fof(f2057,plain,(
% 5.81/1.15    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0)))) | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),X1) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2056,f1732])).
% 5.81/1.15  fof(f2056,plain,(
% 5.81/1.15    ( ! [X0,X1] : (~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0)))) | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),X1) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2050,f115])).
% 5.81/1.15  fof(f2050,plain,(
% 5.81/1.15    ( ! [X0,X1] : (~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X0)))) | r1_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),X1) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(resolution,[],[f2041,f83])).
% 5.81/1.15  fof(f4077,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4058,f1732])).
% 5.81/1.15  fof(f4058,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0)) | r3_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(resolution,[],[f3902,f2041])).
% 5.81/1.15  fof(f3902,plain,(
% 5.81/1.15    ( ! [X10,X9] : (~r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9)))) | ~m1_subset_1(X10,u1_struct_0(sK0)) | r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3901,f100])).
% 5.81/1.15  fof(f3901,plain,(
% 5.81/1.15    ( ! [X10,X9] : (r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9))) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9)))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3900,f1732])).
% 5.81/1.15  fof(f3900,plain,(
% 5.81/1.15    ( ! [X10,X9] : (r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9))) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X9)),u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9)))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3899,f115])).
% 5.81/1.15  fof(f3899,plain,(
% 5.81/1.15    ( ! [X10,X9] : (r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9))) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X9)),u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9)))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3898,f110])).
% 5.81/1.15  fof(f3898,plain,(
% 5.81/1.15    ( ! [X10,X9] : (r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9))) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X9)),u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9)))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3842,f105])).
% 5.81/1.15  fof(f3842,plain,(
% 5.81/1.15    ( ! [X10,X9] : (r3_lattices(sK0,X10,sK3(sK0,k15_lattice3(sK0,X9))) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X9)),u1_struct_0(sK0)) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X10,a_2_4_lattice3(sK0,sK3(sK0,k15_lattice3(sK0,X9)))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(superposition,[],[f95,f1701])).
% 5.81/1.15  fof(f5076,plain,(
% 5.81/1.15    spl9_108 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_64),
% 5.81/1.15    inference(avatar_split_clause,[],[f4097,f2921,f125,f113,f108,f103,f98,f5073])).
% 5.81/1.15  fof(f5073,plain,(
% 5.81/1.15    spl9_108 <=> r3_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).
% 5.81/1.15  fof(f4097,plain,(
% 5.81/1.15    r3_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_64)),
% 5.81/1.15    inference(superposition,[],[f4077,f2923])).
% 5.81/1.15  fof(f5065,plain,(
% 5.81/1.15    ~spl9_106 | spl9_107 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_25 | ~spl9_29),
% 5.81/1.15    inference(avatar_split_clause,[],[f5051,f1361,f1077,f211,f183,f113,f108,f103,f98,f5062,f5058])).
% 5.81/1.15  fof(f5058,plain,(
% 5.81/1.15    spl9_106 <=> r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_106])])).
% 5.81/1.15  fof(f1361,plain,(
% 5.81/1.15    spl9_29 <=> r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 5.81/1.15  fof(f5051,plain,(
% 5.81/1.15    r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) | ~r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f5038,f185])).
% 5.81/1.15  fof(f5038,plain,(
% 5.81/1.15    r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) | ~r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(superposition,[],[f3858,f213])).
% 5.81/1.15  fof(f3858,plain,(
% 5.81/1.15    ( ! [X1] : (r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1)) | ~r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3857,f100])).
% 5.81/1.15  fof(f3857,plain,(
% 5.81/1.15    ( ! [X1] : (~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1) | v2_struct_0(sK0) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3856,f1079])).
% 5.81/1.15  fof(f3856,plain,(
% 5.81/1.15    ( ! [X1] : (~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1) | v2_struct_0(sK0) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3855,f115])).
% 5.81/1.15  fof(f3855,plain,(
% 5.81/1.15    ( ! [X1] : (~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1) | v2_struct_0(sK0) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3854,f110])).
% 5.81/1.15  fof(f3854,plain,(
% 5.81/1.15    ( ! [X1] : (~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1) | v2_struct_0(sK0) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3847,f105])).
% 5.81/1.15  fof(f3847,plain,(
% 5.81/1.15    ( ! [X1] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1) | v2_struct_0(sK0) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f3830])).
% 5.81/1.15  fof(f3830,plain,(
% 5.81/1.15    ( ! [X1] : (~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),X1) | v2_struct_0(sK0) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k16_lattice3(sK0,X1)) | ~m1_subset_1(k16_lattice3(sK0,X1),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(resolution,[],[f95,f1602])).
% 5.81/1.15  fof(f1602,plain,(
% 5.81/1.15    ( ! [X2] : (~r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1601,f100])).
% 5.81/1.15  fof(f1601,plain,(
% 5.81/1.15    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | ~r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1600,f1079])).
% 5.81/1.15  fof(f1600,plain,(
% 5.81/1.15    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1599,f115])).
% 5.81/1.15  fof(f1599,plain,(
% 5.81/1.15    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1598,f110])).
% 5.81/1.15  fof(f1598,plain,(
% 5.81/1.15    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1597,f105])).
% 5.81/1.15  fof(f1597,plain,(
% 5.81/1.15    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f1596])).
% 5.81/1.15  fof(f1596,plain,(
% 5.81/1.15    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X2) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(resolution,[],[f1368,f96])).
% 5.81/1.15  fof(f1368,plain,(
% 5.81/1.15    ( ! [X0] : (~r2_hidden(X0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0)) ) | (spl9_1 | ~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1367,f100])).
% 5.81/1.15  fof(f1367,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_25 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1366,f1079])).
% 5.81/1.15  fof(f1366,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0) | v2_struct_0(sK0)) ) | (~spl9_4 | ~spl9_29)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1365,f115])).
% 5.81/1.15  fof(f1365,plain,(
% 5.81/1.15    ( ! [X0] : (~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0) | v2_struct_0(sK0)) ) | ~spl9_29),
% 5.81/1.15    inference(resolution,[],[f1363,f83])).
% 5.81/1.15  fof(f1363,plain,(
% 5.81/1.15    r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~spl9_29),
% 5.81/1.15    inference(avatar_component_clause,[],[f1361])).
% 5.81/1.15  fof(f4997,plain,(
% 5.81/1.15    spl9_105 | ~spl9_17 | spl9_1 | ~spl9_15 | ~spl9_37),
% 5.81/1.15    inference(avatar_split_clause,[],[f1509,f1487,f409,f98,f416,f4995])).
% 5.81/1.15  fof(f4995,plain,(
% 5.81/1.15    spl9_105 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),X0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_105])])).
% 5.81/1.15  fof(f1509,plain,(
% 5.81/1.15    ( ! [X0] : (~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),X0)) ) | (spl9_1 | ~spl9_15 | ~spl9_37)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1508,f410])).
% 5.81/1.15  fof(f1508,plain,(
% 5.81/1.15    ( ! [X0] : (~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),X0) | ~v6_lattices(sK0)) ) | (spl9_1 | ~spl9_37)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1495,f100])).
% 5.81/1.15  fof(f1495,plain,(
% 5.81/1.15    ( ! [X0] : (~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k2_lattices(sK0,X0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),X0) | ~v6_lattices(sK0)) ) | ~spl9_37),
% 5.81/1.15    inference(resolution,[],[f1489,f72])).
% 5.81/1.15  fof(f4924,plain,(
% 5.81/1.15    ~spl9_17 | spl9_104 | spl9_1 | spl9_6 | ~spl9_41),
% 5.81/1.15    inference(avatar_split_clause,[],[f1630,f1614,f125,f98,f4922,f416])).
% 5.81/1.15  fof(f4922,plain,(
% 5.81/1.15    spl9_104 <=> ! [X2] : (k2_lattices(sK0,sK3(sK0,X2),sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_104])])).
% 5.81/1.15  fof(f1614,plain,(
% 5.81/1.15    spl9_41 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 5.81/1.15  fof(f1630,plain,(
% 5.81/1.15    ( ! [X2] : (k2_lattices(sK0,sK3(sK0,X2),sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,X2)) | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl9_1 | spl9_6 | ~spl9_41)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1629,f127])).
% 5.81/1.15  fof(f1629,plain,(
% 5.81/1.15    ( ! [X2] : (k2_lattices(sK0,sK3(sK0,X2),sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,X2)) | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_41)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1624,f100])).
% 5.81/1.15  fof(f1624,plain,(
% 5.81/1.15    ( ! [X2] : (k2_lattices(sK0,sK3(sK0,X2),sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,X2)) | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | ~spl9_41),
% 5.81/1.15    inference(resolution,[],[f1615,f68])).
% 5.81/1.15  fof(f1615,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0)) ) | ~spl9_41),
% 5.81/1.15    inference(avatar_component_clause,[],[f1614])).
% 5.81/1.15  fof(f4912,plain,(
% 5.81/1.15    ~spl9_103 | ~spl9_36 | ~spl9_37 | ~spl9_102),
% 5.81/1.15    inference(avatar_split_clause,[],[f4903,f4892,f1487,f1442,f4909])).
% 5.81/1.15  fof(f4909,plain,(
% 5.81/1.15    spl9_103 <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).
% 5.81/1.15  fof(f4903,plain,(
% 5.81/1.15    sK3(sK0,sK3(sK0,k5_lattices(sK0))) != k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (~spl9_36 | ~spl9_37 | ~spl9_102)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4898,f1489])).
% 5.81/1.15  fof(f4898,plain,(
% 5.81/1.15    sK3(sK0,sK3(sK0,k5_lattices(sK0))) != k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | (~spl9_36 | ~spl9_102)),
% 5.81/1.15    inference(superposition,[],[f4893,f1444])).
% 5.81/1.15  fof(f4894,plain,(
% 5.81/1.15    ~spl9_17 | spl9_102 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_15),
% 5.81/1.15    inference(avatar_split_clause,[],[f3500,f409,f125,f113,f108,f103,f98,f4892,f416])).
% 5.81/1.15  fof(f3500,plain,(
% 5.81/1.15    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0))) | ~l1_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_15)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3499,f127])).
% 5.81/1.15  fof(f3499,plain,(
% 5.81/1.15    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0))) | ~l1_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_15)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3498,f100])).
% 5.81/1.15  fof(f3498,plain,(
% 5.81/1.15    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0))) | ~l1_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_15)),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f3495])).
% 5.81/1.15  fof(f3495,plain,(
% 5.81/1.15    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0))) | ~l1_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k15_lattice3(sK0,X0))) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_15)),
% 5.81/1.15    inference(superposition,[],[f67,f1775])).
% 5.81/1.15  fof(f1775,plain,(
% 5.81/1.15    ( ! [X15,X16] : (k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X16)) = k2_lattices(sK0,k15_lattice3(sK0,X16),sK3(sK0,k15_lattice3(sK0,X15)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_15)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1774,f115])).
% 5.81/1.15  fof(f1774,plain,(
% 5.81/1.15    ( ! [X15,X16] : (k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X16)) = k2_lattices(sK0,k15_lattice3(sK0,X16),sK3(sK0,k15_lattice3(sK0,X15))) | ~l3_lattices(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_15)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1773,f410])).
% 5.81/1.15  fof(f1773,plain,(
% 5.81/1.15    ( ! [X15,X16] : (k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X16)) = k2_lattices(sK0,k15_lattice3(sK0,X16),sK3(sK0,k15_lattice3(sK0,X15))) | ~v6_lattices(sK0) | ~l3_lattices(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1747,f100])).
% 5.81/1.15  fof(f1747,plain,(
% 5.81/1.15    ( ! [X15,X16] : (v2_struct_0(sK0) | k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X15)),k15_lattice3(sK0,X16)) = k2_lattices(sK0,k15_lattice3(sK0,X16),sK3(sK0,k15_lattice3(sK0,X15))) | ~v6_lattices(sK0) | ~l3_lattices(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(resolution,[],[f1732,f380])).
% 5.81/1.15  fof(f380,plain,(
% 5.81/1.15    ( ! [X4,X2,X3] : (~m1_subset_1(X3,u1_struct_0(X2)) | v2_struct_0(X2) | k2_lattices(X2,X3,k15_lattice3(X2,X4)) = k2_lattices(X2,k15_lattice3(X2,X4),X3) | ~v6_lattices(X2) | ~l3_lattices(X2)) )),
% 5.81/1.15    inference(subsumption_resolution,[],[f378,f50])).
% 5.81/1.15  fof(f378,plain,(
% 5.81/1.15    ( ! [X4,X2,X3] : (~l1_lattices(X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | v2_struct_0(X2) | k2_lattices(X2,X3,k15_lattice3(X2,X4)) = k2_lattices(X2,k15_lattice3(X2,X4),X3) | ~v6_lattices(X2) | ~l3_lattices(X2)) )),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f364])).
% 5.81/1.15  fof(f364,plain,(
% 5.81/1.15    ( ! [X4,X2,X3] : (~l1_lattices(X2) | ~m1_subset_1(X3,u1_struct_0(X2)) | v2_struct_0(X2) | k2_lattices(X2,X3,k15_lattice3(X2,X4)) = k2_lattices(X2,k15_lattice3(X2,X4),X3) | ~v6_lattices(X2) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 5.81/1.15    inference(resolution,[],[f72,f87])).
% 5.81/1.15  fof(f67,plain,(
% 5.81/1.15    ( ! [X0,X1] : (k2_lattices(X0,sK3(X0,X1),X1) != X1 | ~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k2_lattices(X0,X1,sK3(X0,X1)) != X1 | v2_struct_0(X0) | v13_lattices(X0)) )),
% 5.81/1.15    inference(cnf_transformation,[],[f29])).
% 5.81/1.15  fof(f4829,plain,(
% 5.81/1.15    ~spl9_17 | spl9_101 | spl9_1 | spl9_6 | ~spl9_19),
% 5.81/1.15    inference(avatar_split_clause,[],[f1383,f700,f125,f98,f4827,f416])).
% 5.81/1.15  fof(f4827,plain,(
% 5.81/1.15    spl9_101 <=> ! [X2] : (k2_lattices(sK0,sK3(sK0,sK3(sK0,X2)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,X2))) | ~m1_subset_1(X2,u1_struct_0(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_101])])).
% 5.81/1.15  fof(f700,plain,(
% 5.81/1.15    spl9_19 <=> ! [X2] : (k2_lattices(sK0,sK3(sK0,X2),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 5.81/1.15  fof(f1383,plain,(
% 5.81/1.15    ( ! [X2] : (k2_lattices(sK0,sK3(sK0,sK3(sK0,X2)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,X2))) | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl9_1 | spl9_6 | ~spl9_19)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1382,f127])).
% 5.81/1.15  fof(f1382,plain,(
% 5.81/1.15    ( ! [X2] : (k2_lattices(sK0,sK3(sK0,sK3(sK0,X2)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,X2))) | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_19)),
% 5.81/1.15    inference(subsumption_resolution,[],[f1375,f100])).
% 5.81/1.15  fof(f1375,plain,(
% 5.81/1.15    ( ! [X2] : (k2_lattices(sK0,sK3(sK0,sK3(sK0,X2)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,X2))) | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | ~spl9_19),
% 5.81/1.15    inference(resolution,[],[f701,f68])).
% 5.81/1.15  fof(f701,plain,(
% 5.81/1.15    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,sK3(sK0,X2),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,X2))) ) | ~spl9_19),
% 5.81/1.15    inference(avatar_component_clause,[],[f700])).
% 5.81/1.15  fof(f4409,plain,(
% 5.81/1.15    ~spl9_68 | ~spl9_69 | spl9_100 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 5.81/1.15    inference(avatar_split_clause,[],[f4384,f113,f108,f103,f98,f4407,f3350,f3346])).
% 5.81/1.15  fof(f4407,plain,(
% 5.81/1.15    spl9_100 <=> ! [X0] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).
% 5.81/1.15  fof(f4384,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4383,f100])).
% 5.81/1.15  fof(f4383,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4382,f115])).
% 5.81/1.15  fof(f4382,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f4374])).
% 5.81/1.15  fof(f4374,plain,(
% 5.81/1.15    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X0)) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(resolution,[],[f4369,f59])).
% 5.81/1.15  fof(f4259,plain,(
% 5.81/1.15    spl9_99 | ~spl9_24 | ~spl9_98),
% 5.81/1.15    inference(avatar_split_clause,[],[f4247,f4242,f1036,f4256])).
% 5.81/1.15  fof(f4256,plain,(
% 5.81/1.15    spl9_99 <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_99])])).
% 5.81/1.15  fof(f1036,plain,(
% 5.81/1.15    spl9_24 <=> sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 5.81/1.15  fof(f4247,plain,(
% 5.81/1.15    sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (~spl9_24 | ~spl9_98)),
% 5.81/1.15    inference(superposition,[],[f4243,f1038])).
% 5.81/1.15  fof(f1038,plain,(
% 5.81/1.15    sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~spl9_24),
% 5.81/1.15    inference(avatar_component_clause,[],[f1036])).
% 5.81/1.15  fof(f4244,plain,(
% 5.81/1.15    spl9_98 | ~spl9_68 | ~spl9_69 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6),
% 5.81/1.15    inference(avatar_split_clause,[],[f4117,f125,f113,f108,f103,f98,f3350,f3346,f4242])).
% 5.81/1.15  fof(f4117,plain,(
% 5.81/1.15    ( ! [X0] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4116,f100])).
% 5.81/1.15  fof(f4116,plain,(
% 5.81/1.15    ( ! [X0] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4115,f1732])).
% 5.81/1.15  fof(f4115,plain,(
% 5.81/1.15    ( ! [X0] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0)) | sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4114,f115])).
% 5.81/1.15  fof(f4114,plain,(
% 5.81/1.15    ( ! [X0] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0)) | sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f4106])).
% 5.81/1.15  fof(f4106,plain,(
% 5.81/1.15    ( ! [X0] : (~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k15_lattice3(sK0,X0)),u1_struct_0(sK0)) | sK3(sK0,k15_lattice3(sK0,X0)) = k2_lattices(sK0,sK3(sK0,k15_lattice3(sK0,X0)),sK3(sK0,k15_lattice3(sK0,X0))) | v2_struct_0(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6)),
% 5.81/1.15    inference(resolution,[],[f4100,f59])).
% 5.81/1.15  fof(f4227,plain,(
% 5.81/1.15    spl9_97 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_37 | ~spl9_93),
% 5.81/1.15    inference(avatar_split_clause,[],[f4129,f4119,f1487,f113,f108,f103,f98,f4224])).
% 5.81/1.15  fof(f4224,plain,(
% 5.81/1.15    spl9_97 <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_97])])).
% 5.81/1.15  fof(f4119,plain,(
% 5.81/1.15    spl9_93 <=> r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_93])])).
% 5.81/1.15  fof(f4129,plain,(
% 5.81/1.15    sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_37 | ~spl9_93)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4128,f100])).
% 5.81/1.15  fof(f4128,plain,(
% 5.81/1.15    v2_struct_0(sK0) | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_37 | ~spl9_93)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4127,f105])).
% 5.81/1.15  fof(f4127,plain,(
% 5.81/1.15    ~v10_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (~spl9_3 | ~spl9_4 | ~spl9_37 | ~spl9_93)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4126,f1489])).
% 5.81/1.15  fof(f4126,plain,(
% 5.81/1.15    ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (~spl9_3 | ~spl9_4 | ~spl9_93)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4125,f115])).
% 5.81/1.15  fof(f4125,plain,(
% 5.81/1.15    ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (~spl9_3 | ~spl9_93)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4124,f110])).
% 5.81/1.15  fof(f4124,plain,(
% 5.81/1.15    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~spl9_93),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f4123])).
% 5.81/1.15  fof(f4123,plain,(
% 5.81/1.15    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~spl9_93),
% 5.81/1.15    inference(resolution,[],[f4121,f596])).
% 5.81/1.15  fof(f596,plain,(
% 5.81/1.15    ( ! [X2,X3,X1] : (~r3_lattices(X1,X2,X3) | ~v4_lattice3(X1) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v10_lattices(X1) | v2_struct_0(X1) | sK8(X3,X1,X2) = X3) )),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f595])).
% 5.81/1.15  fof(f595,plain,(
% 5.81/1.15    ( ! [X2,X3,X1] : (~v10_lattices(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r3_lattices(X1,X2,X3) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | sK8(X3,X1,X2) = X3 | v2_struct_0(X1)) )),
% 5.81/1.15    inference(resolution,[],[f96,f89])).
% 5.81/1.15  fof(f89,plain,(
% 5.81/1.15    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ~v10_lattices(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | sK8(X0,X1,X2) = X0 | v2_struct_0(X1)) )),
% 5.81/1.15    inference(cnf_transformation,[],[f43])).
% 5.81/1.15  fof(f4121,plain,(
% 5.81/1.15    r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~spl9_93),
% 5.81/1.15    inference(avatar_component_clause,[],[f4119])).
% 5.81/1.15  fof(f4191,plain,(
% 5.81/1.15    spl9_96 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36),
% 5.81/1.15    inference(avatar_split_clause,[],[f4110,f1442,f125,f113,f108,f103,f98,f4188])).
% 5.81/1.15  fof(f4188,plain,(
% 5.81/1.15    spl9_96 <=> r1_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).
% 5.81/1.15  fof(f4110,plain,(
% 5.81/1.15    r1_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36)),
% 5.81/1.15    inference(superposition,[],[f4100,f1444])).
% 5.81/1.15  fof(f4179,plain,(
% 5.81/1.15    spl9_95 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36),
% 5.81/1.15    inference(avatar_split_clause,[],[f4095,f1442,f125,f113,f108,f103,f98,f4176])).
% 5.81/1.15  fof(f4176,plain,(
% 5.81/1.15    spl9_95 <=> r3_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_95])])).
% 5.81/1.15  fof(f4095,plain,(
% 5.81/1.15    r3_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36)),
% 5.81/1.15    inference(superposition,[],[f4077,f1444])).
% 5.81/1.15  fof(f4134,plain,(
% 5.81/1.15    spl9_94 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_24),
% 5.81/1.15    inference(avatar_split_clause,[],[f4109,f1036,f125,f113,f108,f103,f98,f4131])).
% 5.81/1.15  fof(f4131,plain,(
% 5.81/1.15    spl9_94 <=> r1_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).
% 5.81/1.15  fof(f4109,plain,(
% 5.81/1.15    r1_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_24)),
% 5.81/1.15    inference(superposition,[],[f4100,f1038])).
% 5.81/1.15  fof(f4122,plain,(
% 5.81/1.15    spl9_93 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_24),
% 5.81/1.15    inference(avatar_split_clause,[],[f4094,f1036,f125,f113,f108,f103,f98,f4119])).
% 5.81/1.15  fof(f4094,plain,(
% 5.81/1.15    r3_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_24)),
% 5.81/1.15    inference(superposition,[],[f4077,f1038])).
% 5.81/1.15  fof(f4053,plain,(
% 5.81/1.15    ~spl9_91 | spl9_92 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11 | ~spl9_25 | ~spl9_28),
% 5.81/1.15    inference(avatar_split_clause,[],[f3976,f1334,f1077,f335,f183,f113,f108,f103,f98,f4050,f4046])).
% 5.81/1.15  fof(f4046,plain,(
% 5.81/1.15    spl9_91 <=> r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).
% 5.81/1.15  fof(f4050,plain,(
% 5.81/1.15    spl9_92 <=> r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_92])])).
% 5.81/1.15  fof(f1334,plain,(
% 5.81/1.15    spl9_28 <=> sK3(sK0,k5_lattices(sK0)) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 5.81/1.15  fof(f3976,plain,(
% 5.81/1.15    r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3967,f1079])).
% 5.81/1.15  fof(f3967,plain,(
% 5.81/1.15    r1_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11 | ~spl9_28)),
% 5.81/1.15    inference(superposition,[],[f3853,f1336])).
% 5.81/1.15  fof(f1336,plain,(
% 5.81/1.15    sK3(sK0,k5_lattices(sK0)) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~spl9_28),
% 5.81/1.15    inference(avatar_component_clause,[],[f1334])).
% 5.81/1.15  fof(f4041,plain,(
% 5.81/1.15    spl9_90 | ~spl9_68 | ~spl9_69 | spl9_1 | ~spl9_4 | ~spl9_25 | ~spl9_88),
% 5.81/1.15    inference(avatar_split_clause,[],[f4029,f4021,f1077,f113,f98,f3350,f3346,f4038])).
% 5.81/1.15  fof(f4038,plain,(
% 5.81/1.15    spl9_90 <=> sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).
% 5.81/1.15  fof(f4021,plain,(
% 5.81/1.15    spl9_88 <=> r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).
% 5.81/1.15  fof(f4029,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_4 | ~spl9_25 | ~spl9_88)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4028,f100])).
% 5.81/1.15  fof(f4028,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_25 | ~spl9_88)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4027,f1079])).
% 5.81/1.15  fof(f4027,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_88)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4026,f115])).
% 5.81/1.15  fof(f4026,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | ~spl9_88),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f4025])).
% 5.81/1.15  fof(f4025,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | ~spl9_88),
% 5.81/1.15    inference(resolution,[],[f4023,f59])).
% 5.81/1.15  fof(f4023,plain,(
% 5.81/1.15    r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) | ~spl9_88),
% 5.81/1.15    inference(avatar_component_clause,[],[f4021])).
% 5.81/1.15  fof(f4034,plain,(
% 5.81/1.15    spl9_89 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_87),
% 5.81/1.15    inference(avatar_split_clause,[],[f4019,f4007,f1077,f113,f108,f103,f98,f4031])).
% 5.81/1.15  fof(f4031,plain,(
% 5.81/1.15    spl9_89 <=> sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).
% 5.81/1.15  fof(f4007,plain,(
% 5.81/1.15    spl9_87 <=> r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_87])])).
% 5.81/1.15  fof(f4019,plain,(
% 5.81/1.15    sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_87)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4018,f100])).
% 5.81/1.15  fof(f4018,plain,(
% 5.81/1.15    v2_struct_0(sK0) | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0))) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_87)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4017,f105])).
% 5.81/1.15  fof(f4017,plain,(
% 5.81/1.15    ~v10_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0))) | (~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_87)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4016,f1079])).
% 5.81/1.15  fof(f4016,plain,(
% 5.81/1.15    ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0))) | (~spl9_3 | ~spl9_4 | ~spl9_87)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4015,f115])).
% 5.81/1.15  fof(f4015,plain,(
% 5.81/1.15    ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0))) | (~spl9_3 | ~spl9_87)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4013,f110])).
% 5.81/1.15  fof(f4013,plain,(
% 5.81/1.15    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0))) | ~spl9_87),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f4012])).
% 5.81/1.15  fof(f4012,plain,(
% 5.81/1.15    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,sK3(sK0,k5_lattices(sK0))) | ~spl9_87),
% 5.81/1.15    inference(resolution,[],[f4009,f596])).
% 5.81/1.15  fof(f4009,plain,(
% 5.81/1.15    r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) | ~spl9_87),
% 5.81/1.15    inference(avatar_component_clause,[],[f4007])).
% 5.81/1.15  fof(f4024,plain,(
% 5.81/1.15    spl9_88 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29 | ~spl9_87),
% 5.81/1.15    inference(avatar_split_clause,[],[f4014,f4007,f1361,f1077,f113,f108,f103,f98,f4021])).
% 5.81/1.15  fof(f4014,plain,(
% 5.81/1.15    r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29 | ~spl9_87)),
% 5.81/1.15    inference(subsumption_resolution,[],[f4011,f1079])).
% 5.81/1.15  fof(f4011,plain,(
% 5.81/1.15    r1_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_29 | ~spl9_87)),
% 5.81/1.15    inference(resolution,[],[f4009,f1602])).
% 5.81/1.15  fof(f4010,plain,(
% 5.81/1.15    spl9_87 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28),
% 5.81/1.15    inference(avatar_split_clause,[],[f4000,f1334,f1077,f113,f108,f103,f98,f4007])).
% 5.81/1.15  fof(f4000,plain,(
% 5.81/1.15    r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(forward_demodulation,[],[f3999,f1336])).
% 5.81/1.15  fof(f3999,plain,(
% 5.81/1.15    r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3998,f1079])).
% 5.81/1.15  fof(f3998,plain,(
% 5.81/1.15    ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(forward_demodulation,[],[f3997,f1336])).
% 5.81/1.15  fof(f3997,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3996,f100])).
% 5.81/1.15  fof(f3996,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3995,f115])).
% 5.81/1.15  fof(f3995,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0))) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3994,f110])).
% 5.81/1.15  fof(f3994,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3992,f105])).
% 5.81/1.15  fof(f3992,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0))) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f3982])).
% 5.81/1.15  fof(f3982,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),sK3(sK0,k5_lattices(sK0))) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(resolution,[],[f3882,f94])).
% 5.81/1.15  fof(f3882,plain,(
% 5.81/1.15    ( ! [X4] : (~r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3881,f100])).
% 5.81/1.15  fof(f3881,plain,(
% 5.81/1.15    ( ! [X4] : (r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_28)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3880,f1079])).
% 5.81/1.15  fof(f3880,plain,(
% 5.81/1.15    ( ! [X4] : (r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0))) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_28)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3879,f115])).
% 5.81/1.15  fof(f3879,plain,(
% 5.81/1.15    ( ! [X4] : (r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0))) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_28)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3878,f110])).
% 5.81/1.15  fof(f3878,plain,(
% 5.81/1.15    ( ! [X4] : (r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_28)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3838,f105])).
% 5.81/1.15  fof(f3838,plain,(
% 5.81/1.15    ( ! [X4] : (r3_lattices(sK0,X4,sK3(sK0,k5_lattices(sK0))) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X4,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0)) ) | ~spl9_28),
% 5.81/1.15    inference(superposition,[],[f95,f1336])).
% 5.81/1.15  fof(f3959,plain,(
% 5.81/1.15    spl9_86 | ~spl9_68 | ~spl9_69 | spl9_1 | ~spl9_4 | ~spl9_8 | ~spl9_84),
% 5.81/1.15    inference(avatar_split_clause,[],[f3947,f3939,f183,f113,f98,f3350,f3346,f3956])).
% 5.81/1.15  fof(f3956,plain,(
% 5.81/1.15    spl9_86 <=> k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).
% 5.81/1.15  fof(f3939,plain,(
% 5.81/1.15    spl9_84 <=> r1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).
% 5.81/1.15  fof(f3947,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | (spl9_1 | ~spl9_4 | ~spl9_8 | ~spl9_84)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3946,f100])).
% 5.81/1.15  fof(f3946,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_8 | ~spl9_84)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3945,f185])).
% 5.81/1.15  fof(f3945,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_84)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3944,f115])).
% 5.81/1.15  fof(f3944,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | v2_struct_0(sK0) | ~spl9_84),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f3943])).
% 5.81/1.15  fof(f3943,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | v2_struct_0(sK0) | ~spl9_84),
% 5.81/1.15    inference(resolution,[],[f3941,f59])).
% 5.81/1.15  fof(f3941,plain,(
% 5.81/1.15    r1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | ~spl9_84),
% 5.81/1.15    inference(avatar_component_clause,[],[f3939])).
% 5.81/1.15  fof(f3952,plain,(
% 5.81/1.15    spl9_85 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_13),
% 5.81/1.15    inference(avatar_split_clause,[],[f3937,f346,f183,f113,f108,f103,f98,f3949])).
% 5.81/1.15  fof(f3949,plain,(
% 5.81/1.15    spl9_85 <=> k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_85])])).
% 5.81/1.15  fof(f346,plain,(
% 5.81/1.15    spl9_13 <=> r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 5.81/1.15  fof(f3937,plain,(
% 5.81/1.15    k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_13)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3936,f100])).
% 5.81/1.15  fof(f3936,plain,(
% 5.81/1.15    v2_struct_0(sK0) | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0)) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_13)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3935,f105])).
% 5.81/1.15  fof(f3935,plain,(
% 5.81/1.15    ~v10_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0)) | (~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_13)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3934,f185])).
% 5.81/1.15  fof(f3934,plain,(
% 5.81/1.15    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0)) | (~spl9_3 | ~spl9_4 | ~spl9_13)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3933,f115])).
% 5.81/1.15  fof(f3933,plain,(
% 5.81/1.15    ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0)) | (~spl9_3 | ~spl9_13)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3931,f110])).
% 5.81/1.15  fof(f3931,plain,(
% 5.81/1.15    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0)) | ~spl9_13),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f3930])).
% 5.81/1.15  fof(f3930,plain,(
% 5.81/1.15    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v10_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k5_lattices(sK0)) | ~spl9_13),
% 5.81/1.15    inference(resolution,[],[f348,f596])).
% 5.81/1.15  fof(f348,plain,(
% 5.81/1.15    r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | ~spl9_13),
% 5.81/1.15    inference(avatar_component_clause,[],[f346])).
% 5.81/1.15  fof(f3942,plain,(
% 5.81/1.15    spl9_84 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11 | ~spl9_13),
% 5.81/1.15    inference(avatar_split_clause,[],[f3932,f346,f335,f183,f113,f108,f103,f98,f3939])).
% 5.81/1.15  fof(f3932,plain,(
% 5.81/1.15    r1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11 | ~spl9_13)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3929,f185])).
% 5.81/1.15  fof(f3929,plain,(
% 5.81/1.15    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | r1_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_11 | ~spl9_13)),
% 5.81/1.15    inference(resolution,[],[f348,f602])).
% 5.81/1.15  fof(f3928,plain,(
% 5.81/1.15    spl9_13 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9),
% 5.81/1.15    inference(avatar_split_clause,[],[f3922,f211,f183,f113,f108,f103,f98,f346])).
% 5.81/1.15  fof(f3922,plain,(
% 5.81/1.15    r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(forward_demodulation,[],[f3921,f213])).
% 5.81/1.15  fof(f3921,plain,(
% 5.81/1.15    r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3920,f185])).
% 5.81/1.15  fof(f3920,plain,(
% 5.81/1.15    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(forward_demodulation,[],[f3919,f213])).
% 5.81/1.15  fof(f3919,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3918,f100])).
% 5.81/1.15  fof(f3918,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | v2_struct_0(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3917,f115])).
% 5.81/1.15  fof(f3917,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3916,f110])).
% 5.81/1.15  fof(f3916,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3914,f105])).
% 5.81/1.15  fof(f3914,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(duplicate_literal_removal,[],[f3904])).
% 5.81/1.15  fof(f3904,plain,(
% 5.81/1.15    ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | r3_lattices(sK0,k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | v2_struct_0(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(resolution,[],[f3873,f94])).
% 5.81/1.15  fof(f3873,plain,(
% 5.81/1.15    ( ! [X0] : (~r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r3_lattices(sK0,X0,k5_lattices(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3872,f100])).
% 5.81/1.15  fof(f3872,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,X0,k5_lattices(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3871,f185])).
% 5.81/1.15  fof(f3871,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,X0,k5_lattices(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3870,f115])).
% 5.81/1.15  fof(f3870,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,X0,k5_lattices(sK0)) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_9)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3869,f110])).
% 5.81/1.15  fof(f3869,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,X0,k5_lattices(sK0)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_9)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3835,f105])).
% 5.81/1.15  fof(f3835,plain,(
% 5.81/1.15    ( ! [X0] : (r3_lattices(sK0,X0,k5_lattices(sK0)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_lattice3(sK0,X0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | ~spl9_9),
% 5.81/1.15    inference(superposition,[],[f95,f213])).
% 5.81/1.15  fof(f3722,plain,(
% 5.81/1.15    spl9_83 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_64),
% 5.81/1.15    inference(avatar_split_clause,[],[f2973,f2921,f125,f113,f108,f103,f98,f3719])).
% 5.81/1.15  fof(f3719,plain,(
% 5.81/1.15    spl9_83 <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))))),u1_struct_0(sK0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).
% 5.81/1.15  fof(f2973,plain,(
% 5.81/1.15    m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))))),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_64)),
% 5.81/1.15    inference(superposition,[],[f1995,f2923])).
% 5.81/1.15  fof(f3707,plain,(
% 5.81/1.15    spl9_82 | ~spl9_62 | ~spl9_68 | ~spl9_69 | spl9_1 | ~spl9_4 | ~spl9_25 | ~spl9_74),
% 5.81/1.15    inference(avatar_split_clause,[],[f3566,f3559,f1077,f113,f98,f3350,f3346,f2784,f3704])).
% 5.81/1.15  fof(f3704,plain,(
% 5.81/1.15    spl9_82 <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).
% 5.81/1.15  fof(f3559,plain,(
% 5.81/1.15    spl9_74 <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).
% 5.81/1.15  fof(f3566,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_4 | ~spl9_25 | ~spl9_74)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3565,f100])).
% 5.81/1.15  fof(f3565,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_25 | ~spl9_74)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3564,f1079])).
% 5.81/1.15  fof(f3564,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_74)),
% 5.81/1.15    inference(subsumption_resolution,[],[f3563,f115])).
% 5.81/1.15  fof(f3563,plain,(
% 5.81/1.15    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | ~spl9_74),
% 5.81/1.15    inference(resolution,[],[f3561,f59])).
% 5.81/1.15  fof(f3561,plain,(
% 5.81/1.15    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | ~spl9_74),
% 5.81/1.15    inference(avatar_component_clause,[],[f3559])).
% 5.81/1.15  fof(f3696,plain,(
% 5.81/1.15    spl9_81 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_64),
% 5.81/1.15    inference(avatar_split_clause,[],[f2979,f2921,f113,f108,f103,f98,f3693])).
% 5.81/1.15  fof(f3693,plain,(
% 5.81/1.15    spl9_81 <=> sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = sK8(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK0,k15_lattice3(sK0,k1_xboole_0))),
% 5.81/1.15    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).
% 5.81/1.15  fof(f2979,plain,(
% 5.81/1.15    sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = sK8(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),sK0,k15_lattice3(sK0,k1_xboole_0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_64)),
% 5.81/1.15    inference(superposition,[],[f2657,f2923])).
% 5.81/1.15  fof(f2657,plain,(
% 5.81/1.15    ( ! [X0] : (k15_lattice3(sK0,X0) = sK8(k15_lattice3(sK0,X0),sK0,k15_lattice3(sK0,k1_xboole_0))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2656,f115])).
% 5.81/1.15  fof(f2656,plain,(
% 5.81/1.15    ( ! [X0] : (k15_lattice3(sK0,X0) = sK8(k15_lattice3(sK0,X0),sK0,k15_lattice3(sK0,k1_xboole_0)) | ~l3_lattices(sK0)) ) | (spl9_1 | ~spl9_2 | ~spl9_3)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2655,f100])).
% 5.81/1.15  fof(f2655,plain,(
% 5.81/1.15    ( ! [X0] : (v2_struct_0(sK0) | k15_lattice3(sK0,X0) = sK8(k15_lattice3(sK0,X0),sK0,k15_lattice3(sK0,k1_xboole_0)) | ~l3_lattices(sK0)) ) | (~spl9_2 | ~spl9_3)),
% 5.81/1.15    inference(subsumption_resolution,[],[f2654,f105])).
% 5.81/1.15  fof(f2654,plain,(
% 5.81/1.15    ( ! [X0] : (~v10_lattices(sK0) | v2_struct_0(sK0) | k15_lattice3(sK0,X0) = sK8(k15_lattice3(sK0,X0),sK0,k15_lattice3(sK0,k1_xboole_0)) | ~l3_lattices(sK0)) ) | ~spl9_3),
% 5.81/1.15    inference(resolution,[],[f2653,f110])).
% 5.81/1.16  fof(f2653,plain,(
% 5.81/1.16    ( ! [X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | k15_lattice3(X0,X1) = sK8(k15_lattice3(X0,X1),X0,k15_lattice3(X0,k1_xboole_0)) | ~l3_lattices(X0)) )),
% 5.81/1.16    inference(resolution,[],[f2585,f49])).
% 5.81/1.16  fof(f2585,plain,(
% 5.81/1.16    ( ! [X4,X2,X3] : (~r1_tarski(X3,X4) | ~l3_lattices(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | k15_lattice3(X2,X4) = sK8(k15_lattice3(X2,X4),X2,k15_lattice3(X2,X3)) | ~v4_lattice3(X2)) )),
% 5.81/1.16    inference(subsumption_resolution,[],[f2584,f87])).
% 5.81/1.16  fof(f2584,plain,(
% 5.81/1.16    ( ! [X4,X2,X3] : (~v4_lattice3(X2) | ~l3_lattices(X2) | ~m1_subset_1(k15_lattice3(X2,X4),u1_struct_0(X2)) | ~v10_lattices(X2) | v2_struct_0(X2) | k15_lattice3(X2,X4) = sK8(k15_lattice3(X2,X4),X2,k15_lattice3(X2,X3)) | ~r1_tarski(X3,X4)) )),
% 5.81/1.16    inference(subsumption_resolution,[],[f2573,f87])).
% 5.81/1.16  fof(f2573,plain,(
% 5.81/1.16    ( ! [X4,X2,X3] : (~v4_lattice3(X2) | ~l3_lattices(X2) | ~m1_subset_1(k15_lattice3(X2,X3),u1_struct_0(X2)) | ~m1_subset_1(k15_lattice3(X2,X4),u1_struct_0(X2)) | ~v10_lattices(X2) | v2_struct_0(X2) | k15_lattice3(X2,X4) = sK8(k15_lattice3(X2,X4),X2,k15_lattice3(X2,X3)) | ~r1_tarski(X3,X4)) )),
% 5.81/1.16    inference(duplicate_literal_removal,[],[f2552])).
% 5.81/1.16  fof(f2552,plain,(
% 5.81/1.16    ( ! [X4,X2,X3] : (~v4_lattice3(X2) | ~l3_lattices(X2) | ~m1_subset_1(k15_lattice3(X2,X3),u1_struct_0(X2)) | ~m1_subset_1(k15_lattice3(X2,X4),u1_struct_0(X2)) | ~v10_lattices(X2) | v2_struct_0(X2) | k15_lattice3(X2,X4) = sK8(k15_lattice3(X2,X4),X2,k15_lattice3(X2,X3)) | ~v10_lattices(X2) | ~v4_lattice3(X2) | ~l3_lattices(X2) | ~r1_tarski(X3,X4) | v2_struct_0(X2)) )),
% 5.81/1.16    inference(resolution,[],[f596,f81])).
% 5.81/1.16  fof(f3691,plain,(
% 5.81/1.16    ~spl9_17 | ~spl9_80 | spl9_1 | spl9_6 | ~spl9_25 | ~spl9_79),
% 5.81/1.16    inference(avatar_split_clause,[],[f3682,f3673,f1077,f125,f98,f3688,f416])).
% 5.81/1.16  fof(f3688,plain,(
% 5.81/1.16    spl9_80 <=> sK3(sK0,k5_lattices(sK0)) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).
% 5.81/1.16  fof(f3673,plain,(
% 5.81/1.16    spl9_79 <=> k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).
% 5.81/1.16  fof(f3682,plain,(
% 5.81/1.16    sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~l1_lattices(sK0) | (spl9_1 | spl9_6 | ~spl9_25 | ~spl9_79)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3681,f127])).
% 5.81/1.16  fof(f3681,plain,(
% 5.81/1.16    sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~l1_lattices(sK0) | v13_lattices(sK0) | (spl9_1 | ~spl9_25 | ~spl9_79)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3680,f100])).
% 5.81/1.16  fof(f3680,plain,(
% 5.81/1.16    sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~l1_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0) | (~spl9_25 | ~spl9_79)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3679,f1079])).
% 5.81/1.16  fof(f3679,plain,(
% 5.81/1.16    sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~l1_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0) | ~spl9_79),
% 5.81/1.16    inference(duplicate_literal_removal,[],[f3677])).
% 5.81/1.16  fof(f3677,plain,(
% 5.81/1.16    sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~l1_lattices(sK0) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | sK3(sK0,k5_lattices(sK0)) != k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0) | v13_lattices(sK0) | ~spl9_79),
% 5.81/1.16    inference(superposition,[],[f67,f3675])).
% 5.81/1.16  fof(f3675,plain,(
% 5.81/1.16    k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,k5_lattices(sK0))) | ~spl9_79),
% 5.81/1.16    inference(avatar_component_clause,[],[f3673])).
% 5.81/1.16  fof(f3676,plain,(
% 5.81/1.16    spl9_79 | ~spl9_37 | ~spl9_41),
% 5.81/1.16    inference(avatar_split_clause,[],[f1619,f1614,f1487,f3673])).
% 5.81/1.16  fof(f1619,plain,(
% 5.81/1.16    k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK3(sK0,k5_lattices(sK0))) | (~spl9_37 | ~spl9_41)),
% 5.81/1.16    inference(resolution,[],[f1615,f1489])).
% 5.81/1.16  fof(f3666,plain,(
% 5.81/1.16    spl9_78 | ~spl9_16 | ~spl9_42),
% 5.81/1.16    inference(avatar_split_clause,[],[f1832,f1826,f413,f3663])).
% 5.81/1.16  fof(f3663,plain,(
% 5.81/1.16    spl9_78 <=> k2_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_78])])).
% 5.81/1.16  fof(f413,plain,(
% 5.81/1.16    spl9_16 <=> ! [X21] : (~m1_subset_1(X21,u1_struct_0(sK0)) | k2_lattices(sK0,X21,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X21))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 5.81/1.16  fof(f1832,plain,(
% 5.81/1.16    k2_lattices(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (~spl9_16 | ~spl9_42)),
% 5.81/1.16    inference(resolution,[],[f1828,f414])).
% 5.81/1.16  fof(f414,plain,(
% 5.81/1.16    ( ! [X21] : (~m1_subset_1(X21,u1_struct_0(sK0)) | k2_lattices(sK0,X21,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X21)) ) | ~spl9_16),
% 5.81/1.16    inference(avatar_component_clause,[],[f413])).
% 5.81/1.16  fof(f3596,plain,(
% 5.81/1.16    ~spl9_62 | spl9_77 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_37 | ~spl9_75),
% 5.81/1.16    inference(avatar_split_clause,[],[f3588,f3568,f1487,f113,f108,f103,f98,f3593,f2784])).
% 5.81/1.16  fof(f3568,plain,(
% 5.81/1.16    spl9_75 <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_75])])).
% 5.81/1.16  fof(f3588,plain,(
% 5.81/1.16    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_37 | ~spl9_75)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3586,f1489])).
% 5.81/1.16  fof(f3586,plain,(
% 5.81/1.16    ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_75)),
% 5.81/1.16    inference(resolution,[],[f3570,f3280])).
% 5.81/1.16  fof(f3570,plain,(
% 5.81/1.16    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~spl9_75),
% 5.81/1.16    inference(avatar_component_clause,[],[f3568])).
% 5.81/1.16  fof(f3585,plain,(
% 5.81/1.16    spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_36 | spl9_75),
% 5.81/1.16    inference(avatar_contradiction_clause,[],[f3584])).
% 5.81/1.16  fof(f3584,plain,(
% 5.81/1.16    $false | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_36 | spl9_75)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3583,f49])).
% 5.81/1.16  fof(f3583,plain,(
% 5.81/1.16    ~r1_tarski(k1_xboole_0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_36 | spl9_75)),
% 5.81/1.16    inference(resolution,[],[f3569,f1451])).
% 5.81/1.16  fof(f1451,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~r1_tarski(X0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_36)),
% 5.81/1.16    inference(superposition,[],[f264,f1444])).
% 5.81/1.16  fof(f3569,plain,(
% 5.81/1.16    ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | spl9_75),
% 5.81/1.16    inference(avatar_component_clause,[],[f3568])).
% 5.81/1.16  fof(f3582,plain,(
% 5.81/1.16    ~spl9_75 | ~spl9_62 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_37 | spl9_76),
% 5.81/1.16    inference(avatar_split_clause,[],[f3581,f3572,f1487,f113,f108,f103,f98,f2784,f3568])).
% 5.81/1.16  fof(f3572,plain,(
% 5.81/1.16    spl9_76 <=> r2_hidden(sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).
% 5.81/1.16  fof(f3581,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_37 | spl9_76)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3580,f100])).
% 5.81/1.16  fof(f3580,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_37 | spl9_76)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3579,f1489])).
% 5.81/1.16  fof(f3579,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_76)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3578,f115])).
% 5.81/1.16  fof(f3578,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | spl9_76)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3577,f110])).
% 5.81/1.16  fof(f3577,plain,(
% 5.81/1.16    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0) | (~spl9_2 | spl9_76)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3576,f105])).
% 5.81/1.16  fof(f3576,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | v2_struct_0(sK0) | spl9_76),
% 5.81/1.16    inference(resolution,[],[f3574,f96])).
% 5.81/1.16  fof(f3574,plain,(
% 5.81/1.16    ~r2_hidden(sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | spl9_76),
% 5.81/1.16    inference(avatar_component_clause,[],[f3572])).
% 5.81/1.16  fof(f3575,plain,(
% 5.81/1.16    spl9_75 | ~spl9_76 | ~spl9_36 | ~spl9_71),
% 5.81/1.16    inference(avatar_split_clause,[],[f3529,f3522,f1442,f3572,f3568])).
% 5.81/1.16  fof(f3529,plain,(
% 5.81/1.16    ~r2_hidden(sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (~spl9_36 | ~spl9_71)),
% 5.81/1.16    inference(superposition,[],[f3523,f1444])).
% 5.81/1.16  fof(f3562,plain,(
% 5.81/1.16    ~spl9_62 | spl9_74 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_72),
% 5.81/1.16    inference(avatar_split_clause,[],[f3554,f3534,f1077,f113,f108,f103,f98,f3559,f2784])).
% 5.81/1.16  fof(f3534,plain,(
% 5.81/1.16    spl9_72 <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).
% 5.81/1.16  fof(f3554,plain,(
% 5.81/1.16    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | ~spl9_72)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3552,f1079])).
% 5.81/1.16  fof(f3552,plain,(
% 5.81/1.16    ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_72)),
% 5.81/1.16    inference(resolution,[],[f3536,f3280])).
% 5.81/1.16  fof(f3536,plain,(
% 5.81/1.16    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | ~spl9_72),
% 5.81/1.16    inference(avatar_component_clause,[],[f3534])).
% 5.81/1.16  fof(f3551,plain,(
% 5.81/1.16    spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_24 | spl9_72),
% 5.81/1.16    inference(avatar_contradiction_clause,[],[f3550])).
% 5.81/1.16  fof(f3550,plain,(
% 5.81/1.16    $false | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_24 | spl9_72)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3549,f49])).
% 5.81/1.16  fof(f3549,plain,(
% 5.81/1.16    ~r1_tarski(k1_xboole_0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_24 | spl9_72)),
% 5.81/1.16    inference(resolution,[],[f3535,f1296])).
% 5.81/1.16  fof(f1296,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0,k5_lattices(sK0))) | ~r1_tarski(X0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_24)),
% 5.81/1.16    inference(superposition,[],[f264,f1038])).
% 5.81/1.16  fof(f3535,plain,(
% 5.81/1.16    ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | spl9_72),
% 5.81/1.16    inference(avatar_component_clause,[],[f3534])).
% 5.81/1.16  fof(f3548,plain,(
% 5.81/1.16    ~spl9_72 | ~spl9_62 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | spl9_73),
% 5.81/1.16    inference(avatar_split_clause,[],[f3547,f3538,f1077,f113,f108,f103,f98,f2784,f3534])).
% 5.81/1.16  fof(f3538,plain,(
% 5.81/1.16    spl9_73 <=> r2_hidden(sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_73])])).
% 5.81/1.16  fof(f3547,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | spl9_73)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3546,f100])).
% 5.81/1.16  fof(f3546,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25 | spl9_73)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3545,f1079])).
% 5.81/1.16  fof(f3545,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_73)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3544,f115])).
% 5.81/1.16  fof(f3544,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | spl9_73)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3543,f110])).
% 5.81/1.16  fof(f3543,plain,(
% 5.81/1.16    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl9_2 | spl9_73)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3542,f105])).
% 5.81/1.16  fof(f3542,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | spl9_73),
% 5.81/1.16    inference(resolution,[],[f3540,f96])).
% 5.81/1.16  fof(f3540,plain,(
% 5.81/1.16    ~r2_hidden(sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | spl9_73),
% 5.81/1.16    inference(avatar_component_clause,[],[f3538])).
% 5.81/1.16  fof(f3541,plain,(
% 5.81/1.16    spl9_72 | ~spl9_73 | ~spl9_24 | ~spl9_71),
% 5.81/1.16    inference(avatar_split_clause,[],[f3528,f3522,f1036,f3538,f3534])).
% 5.81/1.16  fof(f3528,plain,(
% 5.81/1.16    ~r2_hidden(sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k5_lattices(sK0))) | (~spl9_24 | ~spl9_71)),
% 5.81/1.16    inference(superposition,[],[f3523,f1038])).
% 5.81/1.16  fof(f3524,plain,(
% 5.81/1.16    ~spl9_62 | spl9_71 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 5.81/1.16    inference(avatar_split_clause,[],[f2669,f113,f108,f103,f98,f3522,f2784])).
% 5.81/1.16  fof(f2669,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2668,f100])).
% 5.81/1.16  fof(f2668,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2667,f115])).
% 5.81/1.16  fof(f2667,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2666,f110])).
% 5.81/1.16  fof(f2666,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2664,f105])).
% 5.81/1.16  fof(f2664,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(k15_lattice3(sK0,X0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.16    inference(superposition,[],[f90,f2657])).
% 5.81/1.16  fof(f90,plain,(
% 5.81/1.16    ( ! [X2,X0,X1] : (r3_lattices(X1,X2,sK8(X0,X1,X2)) | ~v10_lattices(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~r2_hidden(X0,a_2_4_lattice3(X1,X2))) )),
% 5.81/1.16    inference(cnf_transformation,[],[f43])).
% 5.81/1.16  fof(f3367,plain,(
% 5.81/1.16    spl9_1 | ~spl9_2 | ~spl9_4 | spl9_69),
% 5.81/1.16    inference(avatar_contradiction_clause,[],[f3366])).
% 5.81/1.16  fof(f3366,plain,(
% 5.81/1.16    $false | (spl9_1 | ~spl9_2 | ~spl9_4 | spl9_69)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3365,f115])).
% 5.81/1.16  fof(f3365,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | (spl9_1 | ~spl9_2 | spl9_69)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3364,f105])).
% 5.81/1.16  fof(f3364,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl9_1 | spl9_69)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3363,f100])).
% 5.81/1.16  fof(f3363,plain,(
% 5.81/1.16    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl9_69),
% 5.81/1.16    inference(resolution,[],[f3352,f56])).
% 5.81/1.16  fof(f3352,plain,(
% 5.81/1.16    ~v8_lattices(sK0) | spl9_69),
% 5.81/1.16    inference(avatar_component_clause,[],[f3350])).
% 5.81/1.16  fof(f3362,plain,(
% 5.81/1.16    spl9_1 | ~spl9_2 | ~spl9_4 | spl9_68),
% 5.81/1.16    inference(avatar_contradiction_clause,[],[f3361])).
% 5.81/1.16  fof(f3361,plain,(
% 5.81/1.16    $false | (spl9_1 | ~spl9_2 | ~spl9_4 | spl9_68)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3360,f115])).
% 5.81/1.16  fof(f3360,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | (spl9_1 | ~spl9_2 | spl9_68)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3359,f105])).
% 5.81/1.16  fof(f3359,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl9_1 | spl9_68)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3358,f100])).
% 5.81/1.16  fof(f3358,plain,(
% 5.81/1.16    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl9_68),
% 5.81/1.16    inference(resolution,[],[f3348,f57])).
% 5.81/1.16  fof(f3348,plain,(
% 5.81/1.16    ~v9_lattices(sK0) | spl9_68),
% 5.81/1.16    inference(avatar_component_clause,[],[f3346])).
% 5.81/1.16  fof(f3357,plain,(
% 5.81/1.16    ~spl9_62 | ~spl9_68 | ~spl9_69 | spl9_70 | spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_8 | ~spl9_67),
% 5.81/1.16    inference(avatar_split_clause,[],[f3294,f3286,f183,f113,f103,f98,f3354,f3350,f3346,f2784])).
% 5.81/1.16  fof(f3354,plain,(
% 5.81/1.16    spl9_70 <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,k1_xboole_0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).
% 5.81/1.16  fof(f3286,plain,(
% 5.81/1.16    spl9_67 <=> r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).
% 5.81/1.16  fof(f3294,plain,(
% 5.81/1.16    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,k1_xboole_0)) | ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_4 | ~spl9_8 | ~spl9_67)),
% 5.81/1.16    inference(forward_demodulation,[],[f3293,f406])).
% 5.81/1.16  fof(f406,plain,(
% 5.81/1.16    ( ! [X0] : (k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))) ) | (spl9_1 | ~spl9_2 | ~spl9_4)),
% 5.81/1.16    inference(subsumption_resolution,[],[f405,f115])).
% 5.81/1.16  fof(f405,plain,(
% 5.81/1.16    ( ! [X0] : (~l3_lattices(sK0) | k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))) ) | (spl9_1 | ~spl9_2)),
% 5.81/1.16    inference(subsumption_resolution,[],[f404,f100])).
% 5.81/1.16  fof(f404,plain,(
% 5.81/1.16    ( ! [X0] : (v2_struct_0(sK0) | ~l3_lattices(sK0) | k2_lattices(sK0,k5_lattices(sK0),k15_lattice3(sK0,X0)) = k2_lattices(sK0,k15_lattice3(sK0,X0),k5_lattices(sK0))) ) | ~spl9_2),
% 5.81/1.16    inference(resolution,[],[f403,f105])).
% 5.81/1.16  fof(f403,plain,(
% 5.81/1.16    ( ! [X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | k2_lattices(X0,k5_lattices(X0),k15_lattice3(X0,X1)) = k2_lattices(X0,k15_lattice3(X0,X1),k5_lattices(X0))) )),
% 5.81/1.16    inference(duplicate_literal_removal,[],[f402])).
% 5.81/1.16  fof(f402,plain,(
% 5.81/1.16    ( ! [X0,X1] : (k2_lattices(X0,k5_lattices(X0),k15_lattice3(X0,X1)) = k2_lattices(X0,k15_lattice3(X0,X1),k5_lattices(X0)) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 5.81/1.16    inference(resolution,[],[f400,f54])).
% 5.81/1.16  fof(f54,plain,(
% 5.81/1.16    ( ! [X0] : (v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 5.81/1.16    inference(cnf_transformation,[],[f21])).
% 5.81/1.16  fof(f400,plain,(
% 5.81/1.16    ( ! [X2,X1] : (~v6_lattices(X1) | k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1)) = k2_lattices(X1,k5_lattices(X1),k15_lattice3(X1,X2)) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 5.81/1.16    inference(subsumption_resolution,[],[f398,f50])).
% 5.81/1.16  fof(f398,plain,(
% 5.81/1.16    ( ! [X2,X1] : (~l1_lattices(X1) | v2_struct_0(X1) | k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1)) = k2_lattices(X1,k5_lattices(X1),k15_lattice3(X1,X2)) | ~v6_lattices(X1) | ~l3_lattices(X1)) )),
% 5.81/1.16    inference(duplicate_literal_removal,[],[f384])).
% 5.81/1.16  fof(f384,plain,(
% 5.81/1.16    ( ! [X2,X1] : (~l1_lattices(X1) | v2_struct_0(X1) | k2_lattices(X1,k15_lattice3(X1,X2),k5_lattices(X1)) = k2_lattices(X1,k5_lattices(X1),k15_lattice3(X1,X2)) | ~v6_lattices(X1) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 5.81/1.16    inference(resolution,[],[f379,f87])).
% 5.81/1.16  fof(f379,plain,(
% 5.81/1.16    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0) | k2_lattices(X0,X1,k5_lattices(X0)) = k2_lattices(X0,k5_lattices(X0),X1) | ~v6_lattices(X0)) )),
% 5.81/1.16    inference(duplicate_literal_removal,[],[f363])).
% 5.81/1.16  fof(f363,plain,(
% 5.81/1.16    ( ! [X0,X1] : (~l1_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | k2_lattices(X0,X1,k5_lattices(X0)) = k2_lattices(X0,k5_lattices(X0),X1) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.81/1.16    inference(resolution,[],[f72,f60])).
% 5.81/1.16  fof(f3293,plain,(
% 5.81/1.16    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl9_1 | ~spl9_4 | ~spl9_8 | ~spl9_67)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3292,f100])).
% 5.81/1.16  fof(f3292,plain,(
% 5.81/1.16    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_8 | ~spl9_67)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3291,f185])).
% 5.81/1.16  fof(f3291,plain,(
% 5.81/1.16    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_67)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3290,f115])).
% 5.81/1.16  fof(f3290,plain,(
% 5.81/1.16    ~v8_lattices(sK0) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | ~spl9_67),
% 5.81/1.16    inference(resolution,[],[f3288,f59])).
% 5.81/1.16  fof(f3288,plain,(
% 5.81/1.16    r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl9_67),
% 5.81/1.16    inference(avatar_component_clause,[],[f3286])).
% 5.81/1.16  fof(f3289,plain,(
% 5.81/1.16    spl9_67 | ~spl9_62 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_61),
% 5.81/1.16    inference(avatar_split_clause,[],[f3281,f2780,f183,f113,f108,f103,f98,f2784,f3286])).
% 5.81/1.16  fof(f2780,plain,(
% 5.81/1.16    spl9_61 <=> r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).
% 5.81/1.16  fof(f3281,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_61)),
% 5.81/1.16    inference(subsumption_resolution,[],[f3268,f185])).
% 5.81/1.16  fof(f3268,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_61)),
% 5.81/1.16    inference(resolution,[],[f3088,f2781])).
% 5.81/1.16  fof(f2781,plain,(
% 5.81/1.16    r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~spl9_61),
% 5.81/1.16    inference(avatar_component_clause,[],[f2780])).
% 5.81/1.16  fof(f3032,plain,(
% 5.81/1.16    spl9_66 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36),
% 5.81/1.16    inference(avatar_split_clause,[],[f2054,f1442,f125,f113,f108,f103,f98,f3029])).
% 5.81/1.16  fof(f3029,plain,(
% 5.81/1.16    spl9_66 <=> r3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).
% 5.81/1.16  fof(f2054,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36)),
% 5.81/1.16    inference(superposition,[],[f2041,f1444])).
% 5.81/1.16  fof(f2999,plain,(
% 5.81/1.16    spl9_65 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42),
% 5.81/1.16    inference(avatar_split_clause,[],[f1858,f1826,f113,f108,f103,f98,f2996])).
% 5.81/1.16  fof(f2996,plain,(
% 5.81/1.16    spl9_65 <=> sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).
% 5.81/1.16  fof(f1858,plain,(
% 5.81/1.16    sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1857,f100])).
% 5.81/1.16  fof(f1857,plain,(
% 5.81/1.16    v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1856,f115])).
% 5.81/1.16  fof(f1856,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (~spl9_2 | ~spl9_3 | ~spl9_42)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1855,f110])).
% 5.81/1.16  fof(f1855,plain,(
% 5.81/1.16    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (~spl9_2 | ~spl9_42)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1837,f105])).
% 5.81/1.16  fof(f1837,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | ~spl9_42),
% 5.81/1.16    inference(resolution,[],[f1828,f75])).
% 5.81/1.16  fof(f2924,plain,(
% 5.81/1.16    spl9_64 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42),
% 5.81/1.16    inference(avatar_split_clause,[],[f1854,f1826,f113,f108,f103,f98,f2921])).
% 5.81/1.16  fof(f1854,plain,(
% 5.81/1.16    sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1853,f100])).
% 5.81/1.16  fof(f1853,plain,(
% 5.81/1.16    v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_42)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1852,f115])).
% 5.81/1.16  fof(f1852,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (~spl9_2 | ~spl9_3 | ~spl9_42)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1851,f110])).
% 5.81/1.16  fof(f1851,plain,(
% 5.81/1.16    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | (~spl9_2 | ~spl9_42)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1836,f105])).
% 5.81/1.16  fof(f1836,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))) | ~spl9_42),
% 5.81/1.16    inference(resolution,[],[f1828,f74])).
% 5.81/1.16  fof(f2805,plain,(
% 5.81/1.16    spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7 | spl9_63),
% 5.81/1.16    inference(avatar_contradiction_clause,[],[f2804])).
% 5.81/1.16  fof(f2804,plain,(
% 5.81/1.16    $false | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7 | spl9_63)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2803,f49])).
% 5.81/1.16  fof(f2803,plain,(
% 5.81/1.16    ~r1_tarski(k1_xboole_0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7 | spl9_63)),
% 5.81/1.16    inference(resolution,[],[f2789,f225])).
% 5.81/1.16  fof(f2789,plain,(
% 5.81/1.16    ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | spl9_63),
% 5.81/1.16    inference(avatar_component_clause,[],[f2788])).
% 5.81/1.16  fof(f2788,plain,(
% 5.81/1.16    spl9_63 <=> r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_63])])).
% 5.81/1.16  fof(f2802,plain,(
% 5.81/1.16    spl9_1 | ~spl9_4 | spl9_62),
% 5.81/1.16    inference(avatar_contradiction_clause,[],[f2801])).
% 5.81/1.16  fof(f2801,plain,(
% 5.81/1.16    $false | (spl9_1 | ~spl9_4 | spl9_62)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2800,f100])).
% 5.81/1.16  fof(f2800,plain,(
% 5.81/1.16    v2_struct_0(sK0) | (~spl9_4 | spl9_62)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2799,f115])).
% 5.81/1.16  fof(f2799,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl9_62),
% 5.81/1.16    inference(resolution,[],[f2786,f87])).
% 5.81/1.16  fof(f2786,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl9_62),
% 5.81/1.16    inference(avatar_component_clause,[],[f2784])).
% 5.81/1.16  fof(f2798,plain,(
% 5.81/1.16    ~spl9_63 | ~spl9_62 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | spl9_61),
% 5.81/1.16    inference(avatar_split_clause,[],[f2797,f2780,f183,f113,f108,f103,f98,f2784,f2788])).
% 5.81/1.16  fof(f2797,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | spl9_61)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2796,f100])).
% 5.81/1.16  fof(f2796,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | spl9_61)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2795,f185])).
% 5.81/1.16  fof(f2795,plain,(
% 5.81/1.16    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_61)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2794,f115])).
% 5.81/1.16  fof(f2794,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | spl9_61)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2793,f110])).
% 5.81/1.16  fof(f2793,plain,(
% 5.81/1.16    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | (~spl9_2 | spl9_61)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2792,f105])).
% 5.81/1.16  fof(f2792,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | v2_struct_0(sK0) | spl9_61),
% 5.81/1.16    inference(resolution,[],[f2782,f96])).
% 5.81/1.16  fof(f2782,plain,(
% 5.81/1.16    ~r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | spl9_61),
% 5.81/1.16    inference(avatar_component_clause,[],[f2780])).
% 5.81/1.16  fof(f2791,plain,(
% 5.81/1.16    ~spl9_61 | ~spl9_62 | spl9_63 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_58),
% 5.81/1.16    inference(avatar_split_clause,[],[f2680,f2671,f113,f108,f103,f98,f2788,f2784,f2780])).
% 5.81/1.16  fof(f2671,plain,(
% 5.81/1.16    spl9_58 <=> k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k15_lattice3(sK0,k1_xboole_0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).
% 5.81/1.16  fof(f2680,plain,(
% 5.81/1.16    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_58)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2679,f100])).
% 5.81/1.16  fof(f2679,plain,(
% 5.81/1.16    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_58)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2678,f115])).
% 5.81/1.16  fof(f2678,plain,(
% 5.81/1.16    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | (~spl9_2 | ~spl9_3 | ~spl9_58)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2677,f110])).
% 5.81/1.16  fof(f2677,plain,(
% 5.81/1.16    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | (~spl9_2 | ~spl9_58)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2675,f105])).
% 5.81/1.16  fof(f2675,plain,(
% 5.81/1.16    r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(k5_lattices(sK0),a_2_4_lattice3(sK0,k15_lattice3(sK0,k1_xboole_0))) | ~spl9_58),
% 5.81/1.16    inference(superposition,[],[f90,f2673])).
% 5.81/1.16  fof(f2673,plain,(
% 5.81/1.16    k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k15_lattice3(sK0,k1_xboole_0)) | ~spl9_58),
% 5.81/1.16    inference(avatar_component_clause,[],[f2671])).
% 5.81/1.16  fof(f2708,plain,(
% 5.81/1.16    spl9_60 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_36),
% 5.81/1.16    inference(avatar_split_clause,[],[f2661,f1442,f113,f108,f103,f98,f2705])).
% 5.81/1.16  fof(f2705,plain,(
% 5.81/1.16    spl9_60 <=> sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,k15_lattice3(sK0,k1_xboole_0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).
% 5.81/1.16  fof(f2661,plain,(
% 5.81/1.16    sK3(sK0,sK3(sK0,k5_lattices(sK0))) = sK8(sK3(sK0,sK3(sK0,k5_lattices(sK0))),sK0,k15_lattice3(sK0,k1_xboole_0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_36)),
% 5.81/1.16    inference(superposition,[],[f2657,f1444])).
% 5.81/1.16  fof(f2685,plain,(
% 5.81/1.16    spl9_59 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_24),
% 5.81/1.16    inference(avatar_split_clause,[],[f2660,f1036,f113,f108,f103,f98,f2682])).
% 5.81/1.16  fof(f2682,plain,(
% 5.81/1.16    spl9_59 <=> sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,k15_lattice3(sK0,k1_xboole_0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).
% 5.81/1.16  fof(f2660,plain,(
% 5.81/1.16    sK3(sK0,k5_lattices(sK0)) = sK8(sK3(sK0,k5_lattices(sK0)),sK0,k15_lattice3(sK0,k1_xboole_0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_24)),
% 5.81/1.16    inference(superposition,[],[f2657,f1038])).
% 5.81/1.16  fof(f2674,plain,(
% 5.81/1.16    spl9_58 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7),
% 5.81/1.16    inference(avatar_split_clause,[],[f2658,f175,f113,f108,f103,f98,f2671])).
% 5.81/1.16  fof(f2658,plain,(
% 5.81/1.16    k5_lattices(sK0) = sK8(k5_lattices(sK0),sK0,k15_lattice3(sK0,k1_xboole_0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7)),
% 5.81/1.16    inference(superposition,[],[f2657,f177])).
% 5.81/1.16  fof(f2549,plain,(
% 5.81/1.16    ~spl9_17 | ~spl9_57 | spl9_1 | spl9_6 | ~spl9_8 | ~spl9_21),
% 5.81/1.16    inference(avatar_split_clause,[],[f2544,f837,f183,f125,f98,f2546,f416])).
% 5.81/1.16  fof(f2544,plain,(
% 5.81/1.16    k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~l1_lattices(sK0) | (spl9_1 | spl9_6 | ~spl9_8 | ~spl9_21)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2543,f127])).
% 5.81/1.16  fof(f2543,plain,(
% 5.81/1.16    k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~l1_lattices(sK0) | v13_lattices(sK0) | (spl9_1 | ~spl9_8 | ~spl9_21)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2542,f100])).
% 5.81/1.16  fof(f2542,plain,(
% 5.81/1.16    k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~l1_lattices(sK0) | v2_struct_0(sK0) | v13_lattices(sK0) | (~spl9_8 | ~spl9_21)),
% 5.81/1.16    inference(subsumption_resolution,[],[f2541,f185])).
% 5.81/1.16  fof(f2541,plain,(
% 5.81/1.16    k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0) | ~spl9_21),
% 5.81/1.16    inference(duplicate_literal_removal,[],[f2540])).
% 5.81/1.16  fof(f2540,plain,(
% 5.81/1.16    k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~l1_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | v13_lattices(sK0) | ~spl9_21),
% 5.81/1.16    inference(superposition,[],[f67,f839])).
% 5.81/1.16  fof(f2445,plain,(
% 5.81/1.16    spl9_56 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36),
% 5.81/1.16    inference(avatar_split_clause,[],[f2130,f1442,f125,f113,f108,f103,f98,f2442])).
% 5.81/1.16  fof(f2442,plain,(
% 5.81/1.16    spl9_56 <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))),u1_struct_0(sK0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).
% 5.81/1.16  fof(f2130,plain,(
% 5.81/1.16    m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))))),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36)),
% 5.81/1.16    inference(superposition,[],[f1995,f1444])).
% 5.81/1.16  fof(f2440,plain,(
% 5.81/1.16    spl9_49 | ~spl9_55 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_24),
% 5.81/1.16    inference(avatar_split_clause,[],[f1308,f1036,f211,f113,f108,f103,f98,f2437,f2409])).
% 5.81/1.16  fof(f2409,plain,(
% 5.81/1.16    spl9_49 <=> r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 5.81/1.16  fof(f2437,plain,(
% 5.81/1.16    spl9_55 <=> r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).
% 5.81/1.16  fof(f1308,plain,(
% 5.81/1.16    ~r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_24)),
% 5.81/1.16    inference(superposition,[],[f311,f1038])).
% 5.81/1.16  fof(f2435,plain,(
% 5.81/1.16    spl9_47 | ~spl9_54 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_24),
% 5.81/1.16    inference(avatar_split_clause,[],[f1305,f1036,f211,f113,f108,f103,f98,f2432,f2400])).
% 5.81/1.16  fof(f2400,plain,(
% 5.81/1.16    spl9_47 <=> r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 5.81/1.16  fof(f2432,plain,(
% 5.81/1.16    spl9_54 <=> r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).
% 5.81/1.16  fof(f1305,plain,(
% 5.81/1.16    ~r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,k5_lattices(sK0))) | r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_24)),
% 5.81/1.16    inference(superposition,[],[f305,f1038])).
% 5.81/1.16  fof(f2430,plain,(
% 5.81/1.16    spl9_52 | ~spl9_53 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23 | ~spl9_24),
% 5.81/1.16    inference(avatar_split_clause,[],[f1422,f1036,f981,f113,f108,f103,f98,f2427,f2423])).
% 5.81/1.16  fof(f2423,plain,(
% 5.81/1.16    spl9_52 <=> r3_lattices(sK0,sK2(sK0),sK3(sK0,k5_lattices(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_52])])).
% 5.81/1.16  fof(f2427,plain,(
% 5.81/1.16    spl9_53 <=> r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK2(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_53])])).
% 5.81/1.16  fof(f1422,plain,(
% 5.81/1.16    ~r1_tarski(a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK2(sK0))) | r3_lattices(sK0,sK2(sK0),sK3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23 | ~spl9_24)),
% 5.81/1.16    inference(superposition,[],[f1220,f1038])).
% 5.81/1.16  fof(f2421,plain,(
% 5.81/1.16    spl9_50 | ~spl9_51 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23 | ~spl9_24),
% 5.81/1.16    inference(avatar_split_clause,[],[f1419,f1036,f981,f113,f108,f103,f98,f2418,f2414])).
% 5.81/1.16  fof(f2414,plain,(
% 5.81/1.16    spl9_50 <=> r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK2(sK0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).
% 5.81/1.16  fof(f2418,plain,(
% 5.81/1.16    spl9_51 <=> r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).
% 5.81/1.16  fof(f1419,plain,(
% 5.81/1.16    ~r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),sK2(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23 | ~spl9_24)),
% 5.81/1.16    inference(superposition,[],[f1219,f1038])).
% 5.81/1.16  fof(f2412,plain,(
% 5.81/1.16    ~spl9_48 | spl9_49 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7 | ~spl9_24),
% 5.81/1.16    inference(avatar_split_clause,[],[f1292,f1036,f175,f113,f108,f103,f98,f2409,f2405])).
% 5.81/1.16  fof(f2405,plain,(
% 5.81/1.16    spl9_48 <=> r1_tarski(a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_3_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).
% 5.81/1.16  fof(f1292,plain,(
% 5.81/1.16    r3_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) | ~r1_tarski(a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_3_lattice3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7 | ~spl9_24)),
% 5.81/1.16    inference(superposition,[],[f225,f1038])).
% 5.81/1.16  fof(f2403,plain,(
% 5.81/1.16    ~spl9_46 | spl9_47 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7 | ~spl9_24),
% 5.81/1.16    inference(avatar_split_clause,[],[f1291,f1036,f175,f113,f108,f103,f98,f2400,f2396])).
% 5.81/1.16  fof(f2396,plain,(
% 5.81/1.16    spl9_46 <=> r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 5.81/1.16  fof(f1291,plain,(
% 5.81/1.16    r3_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | ~r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7 | ~spl9_24)),
% 5.81/1.16    inference(superposition,[],[f221,f1038])).
% 5.81/1.16  fof(f2170,plain,(
% 5.81/1.16    spl9_45 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36),
% 5.81/1.16    inference(avatar_split_clause,[],[f1994,f1442,f125,f113,f108,f103,f98,f2167])).
% 5.81/1.16  fof(f2167,plain,(
% 5.81/1.16    spl9_45 <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))),u1_struct_0(sK0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_45])])).
% 5.81/1.16  fof(f1994,plain,(
% 5.81/1.16    m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))))),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36)),
% 5.81/1.16    inference(superposition,[],[f1897,f1444])).
% 5.81/1.16  fof(f2063,plain,(
% 5.81/1.16    spl9_44 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36),
% 5.81/1.16    inference(avatar_split_clause,[],[f1896,f1442,f125,f113,f108,f103,f98,f2060])).
% 5.81/1.16  fof(f2060,plain,(
% 5.81/1.16    spl9_44 <=> m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),u1_struct_0(sK0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).
% 5.81/1.16  fof(f1896,plain,(
% 5.81/1.16    m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36)),
% 5.81/1.16    inference(superposition,[],[f1799,f1444])).
% 5.81/1.16  fof(f1927,plain,(
% 5.81/1.16    spl9_43 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36),
% 5.81/1.16    inference(avatar_split_clause,[],[f1798,f1442,f125,f113,f108,f103,f98,f1924])).
% 5.81/1.16  fof(f1798,plain,(
% 5.81/1.16    m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_36)),
% 5.81/1.16    inference(superposition,[],[f1756,f1444])).
% 5.81/1.16  fof(f1829,plain,(
% 5.81/1.16    spl9_42 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_24),
% 5.81/1.16    inference(avatar_split_clause,[],[f1797,f1036,f125,f113,f108,f103,f98,f1826])).
% 5.81/1.16  fof(f1797,plain,(
% 5.81/1.16    m1_subset_1(sK3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_24)),
% 5.81/1.16    inference(superposition,[],[f1756,f1038])).
% 5.81/1.16  fof(f1616,plain,(
% 5.81/1.16    spl9_41 | ~spl9_17 | spl9_1 | ~spl9_15 | ~spl9_25),
% 5.81/1.16    inference(avatar_split_clause,[],[f1268,f1077,f409,f98,f416,f1614])).
% 5.81/1.16  fof(f1268,plain,(
% 5.81/1.16    ( ! [X0] : (~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0)) ) | (spl9_1 | ~spl9_15 | ~spl9_25)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1267,f410])).
% 5.81/1.16  fof(f1267,plain,(
% 5.81/1.16    ( ! [X0] : (~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0) | ~v6_lattices(sK0)) ) | (spl9_1 | ~spl9_25)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1254,f100])).
% 5.81/1.16  fof(f1254,plain,(
% 5.81/1.16    ( ! [X0] : (~l1_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k2_lattices(sK0,X0,sK3(sK0,k5_lattices(sK0))) = k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),X0) | ~v6_lattices(sK0)) ) | ~spl9_25),
% 5.81/1.16    inference(resolution,[],[f1079,f72])).
% 5.81/1.16  fof(f1607,plain,(
% 5.81/1.16    spl9_40 | ~spl9_19 | ~spl9_25),
% 5.81/1.16    inference(avatar_split_clause,[],[f1370,f1077,f700,f1604])).
% 5.81/1.16  fof(f1604,plain,(
% 5.81/1.16    spl9_40 <=> k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0))))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 5.81/1.16  fof(f1370,plain,(
% 5.81/1.16    k2_lattices(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,sK3(sK0,k5_lattices(sK0)))) | (~spl9_19 | ~spl9_25)),
% 5.81/1.16    inference(resolution,[],[f701,f1079])).
% 5.81/1.16  fof(f1557,plain,(
% 5.81/1.16    spl9_39 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_37 | ~spl9_38),
% 5.81/1.16    inference(avatar_split_clause,[],[f1544,f1525,f1487,f113,f108,f103,f98,f1554])).
% 5.81/1.16  fof(f1554,plain,(
% 5.81/1.16    spl9_39 <=> r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0)))))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 5.81/1.16  fof(f1544,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_37 | ~spl9_38)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1543,f100])).
% 5.81/1.16  fof(f1543,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_37 | ~spl9_38)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1542,f1489])).
% 5.81/1.16  fof(f1542,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_38)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1541,f115])).
% 5.81/1.16  fof(f1541,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_38)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1540,f110])).
% 5.81/1.16  fof(f1540,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_38)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1537,f105])).
% 5.81/1.16  fof(f1537,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))),a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl9_38),
% 5.81/1.16    inference(superposition,[],[f94,f1527])).
% 5.81/1.16  fof(f1528,plain,(
% 5.81/1.16    spl9_38 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_36),
% 5.81/1.16    inference(avatar_split_clause,[],[f1455,f1442,f113,f108,f103,f98,f1525])).
% 5.81/1.16  fof(f1455,plain,(
% 5.81/1.16    sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_36)),
% 5.81/1.16    inference(superposition,[],[f281,f1444])).
% 5.81/1.16  fof(f1490,plain,(
% 5.81/1.16    spl9_37 | spl9_1 | ~spl9_4 | ~spl9_36),
% 5.81/1.16    inference(avatar_split_clause,[],[f1485,f1442,f113,f98,f1487])).
% 5.81/1.16  fof(f1485,plain,(
% 5.81/1.16    m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | (spl9_1 | ~spl9_4 | ~spl9_36)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1484,f100])).
% 5.81/1.16  fof(f1484,plain,(
% 5.81/1.16    m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_36)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1475,f115])).
% 5.81/1.16  fof(f1475,plain,(
% 5.81/1.16    m1_subset_1(sK3(sK0,sK3(sK0,k5_lattices(sK0))),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl9_36),
% 5.81/1.16    inference(superposition,[],[f87,f1444])).
% 5.81/1.16  fof(f1445,plain,(
% 5.81/1.16    spl9_36 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_25),
% 5.81/1.16    inference(avatar_split_clause,[],[f1281,f1077,f125,f113,f108,f103,f98,f1442])).
% 5.81/1.16  fof(f1281,plain,(
% 5.81/1.16    sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_25)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1280,f127])).
% 5.81/1.16  fof(f1280,plain,(
% 5.81/1.16    sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | v13_lattices(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_25)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1279,f105])).
% 5.81/1.16  fof(f1279,plain,(
% 5.81/1.16    sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~v10_lattices(sK0) | v13_lattices(sK0) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_25)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1278,f100])).
% 5.81/1.16  fof(f1278,plain,(
% 5.81/1.16    v2_struct_0(sK0) | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~v10_lattices(sK0) | v13_lattices(sK0) | (~spl9_3 | ~spl9_4 | ~spl9_25)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1277,f115])).
% 5.81/1.16  fof(f1277,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~v10_lattices(sK0) | v13_lattices(sK0) | (~spl9_3 | ~spl9_25)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1257,f110])).
% 5.81/1.16  fof(f1257,plain,(
% 5.81/1.16    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,sK3(sK0,k5_lattices(sK0))) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,sK3(sK0,k5_lattices(sK0))))) | ~v10_lattices(sK0) | v13_lattices(sK0) | ~spl9_25),
% 5.81/1.16    inference(resolution,[],[f1079,f169])).
% 5.81/1.16  fof(f1416,plain,(
% 5.81/1.16    ~spl9_34 | spl9_35 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_23),
% 5.81/1.16    inference(avatar_split_clause,[],[f1328,f981,f211,f113,f108,f103,f98,f1413,f1409])).
% 5.81/1.16  fof(f1409,plain,(
% 5.81/1.16    spl9_34 <=> r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK2(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 5.81/1.16  fof(f1413,plain,(
% 5.81/1.16    spl9_35 <=> r3_lattices(sK0,sK2(sK0),k5_lattices(sK0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 5.81/1.16  fof(f1328,plain,(
% 5.81/1.16    r3_lattices(sK0,sK2(sK0),k5_lattices(sK0)) | ~r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK2(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_23)),
% 5.81/1.16    inference(superposition,[],[f1238,f213])).
% 5.81/1.16  fof(f1238,plain,(
% 5.81/1.16    ( ! [X3] : (r3_lattices(sK0,sK2(sK0),k16_lattice3(sK0,X3)) | ~r1_tarski(X3,a_2_4_lattice3(sK0,sK2(sK0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1237,f100])).
% 5.81/1.16  fof(f1237,plain,(
% 5.81/1.16    ( ! [X3] : (r3_lattices(sK0,sK2(sK0),k16_lattice3(sK0,X3)) | ~r1_tarski(X3,a_2_4_lattice3(sK0,sK2(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1236,f115])).
% 5.81/1.16  fof(f1236,plain,(
% 5.81/1.16    ( ! [X3] : (r3_lattices(sK0,sK2(sK0),k16_lattice3(sK0,X3)) | ~l3_lattices(sK0) | ~r1_tarski(X3,a_2_4_lattice3(sK0,sK2(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1235,f110])).
% 5.81/1.16  fof(f1235,plain,(
% 5.81/1.16    ( ! [X3] : (r3_lattices(sK0,sK2(sK0),k16_lattice3(sK0,X3)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X3,a_2_4_lattice3(sK0,sK2(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1225,f105])).
% 5.81/1.16  fof(f1225,plain,(
% 5.81/1.16    ( ! [X3] : (r3_lattices(sK0,sK2(sK0),k16_lattice3(sK0,X3)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X3,a_2_4_lattice3(sK0,sK2(sK0))) | v2_struct_0(sK0)) ) | ~spl9_23),
% 5.81/1.16    inference(superposition,[],[f82,f983])).
% 5.81/1.16  fof(f1407,plain,(
% 5.81/1.16    ~spl9_32 | spl9_33 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_23),
% 5.81/1.16    inference(avatar_split_clause,[],[f1325,f981,f211,f113,f108,f103,f98,f1404,f1400])).
% 5.81/1.16  fof(f1400,plain,(
% 5.81/1.16    spl9_32 <=> r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 5.81/1.16  fof(f1404,plain,(
% 5.81/1.16    spl9_33 <=> r3_lattices(sK0,k5_lattices(sK0),sK2(sK0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 5.81/1.16  fof(f1325,plain,(
% 5.81/1.16    r3_lattices(sK0,k5_lattices(sK0),sK2(sK0)) | ~r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9 | ~spl9_23)),
% 5.81/1.16    inference(superposition,[],[f1234,f213])).
% 5.81/1.16  fof(f1234,plain,(
% 5.81/1.16    ( ! [X2] : (r3_lattices(sK0,k16_lattice3(sK0,X2),sK2(sK0)) | ~r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),X2)) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1233,f100])).
% 5.81/1.16  fof(f1233,plain,(
% 5.81/1.16    ( ! [X2] : (r3_lattices(sK0,k16_lattice3(sK0,X2),sK2(sK0)) | ~r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),X2) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1232,f115])).
% 5.81/1.16  fof(f1232,plain,(
% 5.81/1.16    ( ! [X2] : (r3_lattices(sK0,k16_lattice3(sK0,X2),sK2(sK0)) | ~l3_lattices(sK0) | ~r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),X2) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1231,f110])).
% 5.81/1.16  fof(f1231,plain,(
% 5.81/1.16    ( ! [X2] : (r3_lattices(sK0,k16_lattice3(sK0,X2),sK2(sK0)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),X2) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1224,f105])).
% 5.81/1.16  fof(f1224,plain,(
% 5.81/1.16    ( ! [X2] : (r3_lattices(sK0,k16_lattice3(sK0,X2),sK2(sK0)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),X2) | v2_struct_0(sK0)) ) | ~spl9_23),
% 5.81/1.16    inference(superposition,[],[f82,f983])).
% 5.81/1.16  fof(f1398,plain,(
% 5.81/1.16    ~spl9_30 | spl9_31 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23),
% 5.81/1.16    inference(avatar_split_clause,[],[f1327,f981,f113,f108,f103,f98,f1395,f1391])).
% 5.81/1.16  fof(f1391,plain,(
% 5.81/1.16    spl9_30 <=> r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK2(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 5.81/1.16  fof(f1327,plain,(
% 5.81/1.16    r3_lattices(sK0,sK2(sK0),sK2(sK0)) | ~r1_tarski(a_2_4_lattice3(sK0,sK2(sK0)),a_2_4_lattice3(sK0,sK2(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23)),
% 5.81/1.16    inference(superposition,[],[f1234,f983])).
% 5.81/1.16  fof(f1364,plain,(
% 5.81/1.16    spl9_29 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_24 | ~spl9_25),
% 5.81/1.16    inference(avatar_split_clause,[],[f1316,f1077,f1036,f113,f108,f103,f98,f1361])).
% 5.81/1.16  fof(f1316,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_24 | ~spl9_25)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1309,f1079])).
% 5.81/1.16  fof(f1309,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_24)),
% 5.81/1.16    inference(superposition,[],[f333,f1038])).
% 5.81/1.16  fof(f1337,plain,(
% 5.81/1.16    spl9_28 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_24),
% 5.81/1.16    inference(avatar_split_clause,[],[f1049,f1036,f113,f108,f103,f98,f1334])).
% 5.81/1.16  fof(f1049,plain,(
% 5.81/1.16    sK3(sK0,k5_lattices(sK0)) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_24)),
% 5.81/1.16    inference(superposition,[],[f281,f1038])).
% 5.81/1.16  fof(f1331,plain,(
% 5.81/1.16    ~spl9_20 | spl9_27 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23),
% 5.81/1.16    inference(avatar_split_clause,[],[f1290,f981,f113,f108,f103,f98,f1286,f811])).
% 5.81/1.16  fof(f1286,plain,(
% 5.81/1.16    spl9_27 <=> r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 5.81/1.16  fof(f1290,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0))) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1228,f100])).
% 5.81/1.16  fof(f1228,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0))) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1227,f115])).
% 5.81/1.16  fof(f1227,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0))) | ~l3_lattices(sK0) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1226,f110])).
% 5.81/1.16  fof(f1226,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0))) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_23)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1223,f105])).
% 5.81/1.16  fof(f1223,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0))) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl9_23),
% 5.81/1.16    inference(superposition,[],[f94,f983])).
% 5.81/1.16  fof(f1289,plain,(
% 5.81/1.16    spl9_27 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_10 | ~spl9_20),
% 5.81/1.16    inference(avatar_split_clause,[],[f966,f811,f274,f113,f108,f103,f98,f1286])).
% 5.81/1.16  fof(f966,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_10 | ~spl9_20)),
% 5.81/1.16    inference(subsumption_resolution,[],[f959,f813])).
% 5.81/1.16  fof(f959,plain,(
% 5.81/1.16    r3_lattice3(sK0,sK2(sK0),a_2_4_lattice3(sK0,sK2(sK0))) | ~m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_10)),
% 5.81/1.16    inference(superposition,[],[f333,f276])).
% 5.81/1.16  fof(f1243,plain,(
% 5.81/1.16    ~spl9_17 | spl9_26 | spl9_1 | ~spl9_6),
% 5.81/1.16    inference(avatar_split_clause,[],[f1124,f125,f98,f1240,f416])).
% 5.81/1.16  fof(f1124,plain,(
% 5.81/1.16    sK2(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0)) | ~l1_lattices(sK0) | (spl9_1 | ~spl9_6)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1090,f100])).
% 5.81/1.16  fof(f1090,plain,(
% 5.81/1.16    v2_struct_0(sK0) | sK2(sK0) = k2_lattices(sK0,sK2(sK0),k5_lattices(sK0)) | ~l1_lattices(sK0) | ~spl9_6),
% 5.81/1.16    inference(resolution,[],[f126,f140])).
% 5.81/1.16  fof(f140,plain,(
% 5.81/1.16    ( ! [X0] : (~v13_lattices(X0) | v2_struct_0(X0) | sK2(X0) = k2_lattices(X0,sK2(X0),k5_lattices(X0)) | ~l1_lattices(X0)) )),
% 5.81/1.16    inference(duplicate_literal_removal,[],[f129])).
% 5.81/1.16  fof(f129,plain,(
% 5.81/1.16    ( ! [X0] : (~l1_lattices(X0) | v2_struct_0(X0) | sK2(X0) = k2_lattices(X0,sK2(X0),k5_lattices(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.81/1.16    inference(resolution,[],[f65,f60])).
% 5.81/1.16  fof(f65,plain,(
% 5.81/1.16    ( ! [X2,X0] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0) | sK2(X0) = k2_lattices(X0,sK2(X0),X2) | ~v13_lattices(X0)) )),
% 5.81/1.16    inference(cnf_transformation,[],[f29])).
% 5.81/1.16  fof(f1080,plain,(
% 5.81/1.16    spl9_25 | spl9_1 | ~spl9_4 | ~spl9_24),
% 5.81/1.16    inference(avatar_split_clause,[],[f1075,f1036,f113,f98,f1077])).
% 5.81/1.16  fof(f1075,plain,(
% 5.81/1.16    m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | (spl9_1 | ~spl9_4 | ~spl9_24)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1074,f100])).
% 5.81/1.16  fof(f1074,plain,(
% 5.81/1.16    m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_24)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1065,f115])).
% 5.81/1.16  fof(f1065,plain,(
% 5.81/1.16    m1_subset_1(sK3(sK0,k5_lattices(sK0)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl9_24),
% 5.81/1.16    inference(superposition,[],[f87,f1038])).
% 5.81/1.16  fof(f1039,plain,(
% 5.81/1.16    spl9_24 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_8),
% 5.81/1.16    inference(avatar_split_clause,[],[f1034,f183,f125,f113,f108,f103,f98,f1036])).
% 5.81/1.16  fof(f1034,plain,(
% 5.81/1.16    sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_6 | ~spl9_8)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1033,f127])).
% 5.81/1.16  fof(f1033,plain,(
% 5.81/1.16    sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | v13_lattices(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1032,f105])).
% 5.81/1.16  fof(f1032,plain,(
% 5.81/1.16    sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~v10_lattices(sK0) | v13_lattices(sK0) | (spl9_1 | ~spl9_3 | ~spl9_4 | ~spl9_8)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1031,f100])).
% 5.81/1.16  fof(f1031,plain,(
% 5.81/1.16    v2_struct_0(sK0) | sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~v10_lattices(sK0) | v13_lattices(sK0) | (~spl9_3 | ~spl9_4 | ~spl9_8)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1030,f115])).
% 5.81/1.16  fof(f1030,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~v10_lattices(sK0) | v13_lattices(sK0) | (~spl9_3 | ~spl9_8)),
% 5.81/1.16    inference(subsumption_resolution,[],[f1017,f110])).
% 5.81/1.16  fof(f1017,plain,(
% 5.81/1.16    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK3(sK0,k5_lattices(sK0)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK3(sK0,k5_lattices(sK0)))) | ~v10_lattices(sK0) | v13_lattices(sK0) | ~spl9_8),
% 5.81/1.16    inference(resolution,[],[f169,f185])).
% 5.81/1.16  fof(f986,plain,(
% 5.81/1.16    spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_10 | ~spl9_20),
% 5.81/1.16    inference(avatar_contradiction_clause,[],[f985])).
% 5.81/1.16  fof(f985,plain,(
% 5.81/1.16    $false | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_10 | ~spl9_20)),
% 5.81/1.16    inference(subsumption_resolution,[],[f931,f275])).
% 5.81/1.16  fof(f275,plain,(
% 5.81/1.16    sK2(sK0) != k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) | spl9_10),
% 5.81/1.16    inference(avatar_component_clause,[],[f274])).
% 5.81/1.16  fof(f931,plain,(
% 5.81/1.16    sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_20)),
% 5.81/1.16    inference(subsumption_resolution,[],[f930,f100])).
% 5.81/1.16  fof(f930,plain,(
% 5.81/1.16    v2_struct_0(sK0) | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_20)),
% 5.81/1.16    inference(subsumption_resolution,[],[f929,f115])).
% 5.81/1.16  fof(f929,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) | (~spl9_2 | ~spl9_3 | ~spl9_20)),
% 5.81/1.16    inference(subsumption_resolution,[],[f928,f110])).
% 5.81/1.16  fof(f928,plain,(
% 5.81/1.16    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) | (~spl9_2 | ~spl9_20)),
% 5.81/1.16    inference(subsumption_resolution,[],[f915,f105])).
% 5.81/1.16  fof(f915,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) | ~spl9_20),
% 5.81/1.16    inference(resolution,[],[f813,f74])).
% 5.81/1.16  fof(f984,plain,(
% 5.81/1.16    spl9_23 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_10),
% 5.81/1.16    inference(avatar_split_clause,[],[f784,f274,f113,f108,f103,f98,f981])).
% 5.81/1.16  fof(f784,plain,(
% 5.81/1.16    sK2(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,sK2(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_10)),
% 5.81/1.16    inference(superposition,[],[f281,f276])).
% 5.81/1.16  fof(f979,plain,(
% 5.81/1.16    ~spl9_17 | spl9_22 | spl9_1 | ~spl9_6),
% 5.81/1.16    inference(avatar_split_clause,[],[f880,f125,f98,f976,f416])).
% 5.81/1.16  fof(f976,plain,(
% 5.81/1.16    spl9_22 <=> sK2(sK0) = k2_lattices(sK0,sK2(sK0),sK2(sK0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 5.81/1.16  fof(f880,plain,(
% 5.81/1.16    sK2(sK0) = k2_lattices(sK0,sK2(sK0),sK2(sK0)) | ~l1_lattices(sK0) | (spl9_1 | ~spl9_6)),
% 5.81/1.16    inference(subsumption_resolution,[],[f846,f100])).
% 5.81/1.16  fof(f846,plain,(
% 5.81/1.16    v2_struct_0(sK0) | sK2(sK0) = k2_lattices(sK0,sK2(sK0),sK2(sK0)) | ~l1_lattices(sK0) | ~spl9_6),
% 5.81/1.16    inference(resolution,[],[f126,f138])).
% 5.81/1.16  fof(f138,plain,(
% 5.81/1.16    ( ! [X3] : (~v13_lattices(X3) | v2_struct_0(X3) | sK2(X3) = k2_lattices(X3,sK2(X3),sK2(X3)) | ~l1_lattices(X3)) )),
% 5.81/1.16    inference(duplicate_literal_removal,[],[f131])).
% 5.81/1.16  fof(f131,plain,(
% 5.81/1.16    ( ! [X3] : (~l1_lattices(X3) | v2_struct_0(X3) | sK2(X3) = k2_lattices(X3,sK2(X3),sK2(X3)) | ~v13_lattices(X3) | ~l1_lattices(X3) | v2_struct_0(X3) | ~v13_lattices(X3)) )),
% 5.81/1.16    inference(resolution,[],[f65,f69])).
% 5.81/1.16  fof(f840,plain,(
% 5.81/1.16    spl9_21 | ~spl9_8 | ~spl9_19),
% 5.81/1.16    inference(avatar_split_clause,[],[f815,f700,f183,f837])).
% 5.81/1.16  fof(f815,plain,(
% 5.81/1.16    k2_lattices(sK0,sK3(sK0,k5_lattices(sK0)),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,k5_lattices(sK0))) | (~spl9_8 | ~spl9_19)),
% 5.81/1.16    inference(resolution,[],[f701,f185])).
% 5.81/1.16  fof(f814,plain,(
% 5.81/1.16    spl9_20 | spl9_1 | ~spl9_4 | ~spl9_10),
% 5.81/1.16    inference(avatar_split_clause,[],[f809,f274,f113,f98,f811])).
% 5.81/1.16  fof(f809,plain,(
% 5.81/1.16    m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_4 | ~spl9_10)),
% 5.81/1.16    inference(subsumption_resolution,[],[f808,f100])).
% 5.81/1.16  fof(f808,plain,(
% 5.81/1.16    m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_10)),
% 5.81/1.16    inference(subsumption_resolution,[],[f799,f115])).
% 5.81/1.16  fof(f799,plain,(
% 5.81/1.16    m1_subset_1(sK2(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl9_10),
% 5.81/1.16    inference(superposition,[],[f87,f276])).
% 5.81/1.16  fof(f702,plain,(
% 5.81/1.16    ~spl9_17 | spl9_19 | spl9_1 | spl9_6 | ~spl9_16),
% 5.81/1.16    inference(avatar_split_clause,[],[f438,f413,f125,f98,f700,f416])).
% 5.81/1.16  fof(f438,plain,(
% 5.81/1.16    ( ! [X2] : (k2_lattices(sK0,sK3(sK0,X2),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,X2)) | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (spl9_1 | spl9_6 | ~spl9_16)),
% 5.81/1.16    inference(subsumption_resolution,[],[f437,f127])).
% 5.81/1.16  fof(f437,plain,(
% 5.81/1.16    ( ! [X2] : (k2_lattices(sK0,sK3(sK0,X2),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,X2)) | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v13_lattices(sK0)) ) | (spl9_1 | ~spl9_16)),
% 5.81/1.16    inference(subsumption_resolution,[],[f433,f100])).
% 5.81/1.16  fof(f433,plain,(
% 5.81/1.16    ( ! [X2] : (k2_lattices(sK0,sK3(sK0,X2),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK3(sK0,X2)) | ~l1_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0) | v13_lattices(sK0)) ) | ~spl9_16),
% 5.81/1.16    inference(resolution,[],[f414,f68])).
% 5.81/1.16  fof(f447,plain,(
% 5.81/1.16    spl9_15 | ~spl9_17 | spl9_18 | spl9_1 | ~spl9_16),
% 5.81/1.16    inference(avatar_split_clause,[],[f439,f413,f98,f444,f416,f409])).
% 5.81/1.16  fof(f444,plain,(
% 5.81/1.16    spl9_18 <=> k2_lattices(sK0,sK4(sK0),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 5.81/1.16  fof(f439,plain,(
% 5.81/1.16    k2_lattices(sK0,sK4(sK0),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0)) | ~l1_lattices(sK0) | v6_lattices(sK0) | (spl9_1 | ~spl9_16)),
% 5.81/1.16    inference(subsumption_resolution,[],[f434,f100])).
% 5.81/1.16  fof(f434,plain,(
% 5.81/1.16    k2_lattices(sK0,sK4(sK0),k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | v6_lattices(sK0) | ~spl9_16),
% 5.81/1.16    inference(resolution,[],[f414,f73])).
% 5.81/1.16  fof(f73,plain,(
% 5.81/1.16    ( ! [X0] : (m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0) | v6_lattices(X0)) )),
% 5.81/1.16    inference(cnf_transformation,[],[f31])).
% 5.81/1.16  fof(f427,plain,(
% 5.81/1.16    ~spl9_4 | spl9_17),
% 5.81/1.16    inference(avatar_contradiction_clause,[],[f426])).
% 5.81/1.16  fof(f426,plain,(
% 5.81/1.16    $false | (~spl9_4 | spl9_17)),
% 5.81/1.16    inference(subsumption_resolution,[],[f425,f115])).
% 5.81/1.16  fof(f425,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | spl9_17),
% 5.81/1.16    inference(resolution,[],[f418,f50])).
% 5.81/1.16  fof(f418,plain,(
% 5.81/1.16    ~l1_lattices(sK0) | spl9_17),
% 5.81/1.16    inference(avatar_component_clause,[],[f416])).
% 5.81/1.16  fof(f424,plain,(
% 5.81/1.16    spl9_1 | ~spl9_2 | ~spl9_4 | spl9_15),
% 5.81/1.16    inference(avatar_contradiction_clause,[],[f423])).
% 5.81/1.16  fof(f423,plain,(
% 5.81/1.16    $false | (spl9_1 | ~spl9_2 | ~spl9_4 | spl9_15)),
% 5.81/1.16    inference(subsumption_resolution,[],[f422,f115])).
% 5.81/1.16  fof(f422,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | (spl9_1 | ~spl9_2 | spl9_15)),
% 5.81/1.16    inference(subsumption_resolution,[],[f421,f105])).
% 5.81/1.16  fof(f421,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~l3_lattices(sK0) | (spl9_1 | spl9_15)),
% 5.81/1.16    inference(subsumption_resolution,[],[f420,f100])).
% 5.81/1.16  fof(f420,plain,(
% 5.81/1.16    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~l3_lattices(sK0) | spl9_15),
% 5.81/1.16    inference(resolution,[],[f411,f54])).
% 5.81/1.16  fof(f411,plain,(
% 5.81/1.16    ~v6_lattices(sK0) | spl9_15),
% 5.81/1.16    inference(avatar_component_clause,[],[f409])).
% 5.81/1.16  fof(f419,plain,(
% 5.81/1.16    ~spl9_15 | spl9_16 | ~spl9_17 | spl9_1 | ~spl9_8),
% 5.81/1.16    inference(avatar_split_clause,[],[f382,f183,f98,f416,f413,f409])).
% 5.81/1.16  fof(f382,plain,(
% 5.81/1.16    ( ! [X21] : (~l1_lattices(sK0) | ~m1_subset_1(X21,u1_struct_0(sK0)) | k2_lattices(sK0,X21,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X21) | ~v6_lattices(sK0)) ) | (spl9_1 | ~spl9_8)),
% 5.81/1.16    inference(subsumption_resolution,[],[f371,f100])).
% 5.81/1.16  fof(f371,plain,(
% 5.81/1.16    ( ! [X21] : (~l1_lattices(sK0) | ~m1_subset_1(X21,u1_struct_0(sK0)) | v2_struct_0(sK0) | k2_lattices(sK0,X21,k5_lattices(sK0)) = k2_lattices(sK0,k5_lattices(sK0),X21) | ~v6_lattices(sK0)) ) | ~spl9_8),
% 5.81/1.16    inference(resolution,[],[f72,f185])).
% 5.81/1.16  fof(f354,plain,(
% 5.81/1.16    ~spl9_14 | spl9_13 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9),
% 5.81/1.16    inference(avatar_split_clause,[],[f238,f211,f113,f108,f103,f98,f346,f351])).
% 5.81/1.16  fof(f351,plain,(
% 5.81/1.16    spl9_14 <=> r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 5.81/1.16  fof(f238,plain,(
% 5.81/1.16    r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | ~r1_tarski(a_2_4_lattice3(sK0,k5_lattices(sK0)),a_2_4_lattice3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9)),
% 5.81/1.16    inference(superposition,[],[f233,f213])).
% 5.81/1.16  fof(f233,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) | ~r1_tarski(X0,a_2_4_lattice3(sK0,k5_lattices(sK0)))) ) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9)),
% 5.81/1.16    inference(subsumption_resolution,[],[f232,f100])).
% 5.81/1.16  fof(f232,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) | ~r1_tarski(X0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9)),
% 5.81/1.16    inference(subsumption_resolution,[],[f231,f115])).
% 5.81/1.16  fof(f231,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) | ~l3_lattices(sK0) | ~r1_tarski(X0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_3 | ~spl9_9)),
% 5.81/1.16    inference(subsumption_resolution,[],[f230,f110])).
% 5.81/1.16  fof(f230,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | (~spl9_2 | ~spl9_9)),
% 5.81/1.16    inference(subsumption_resolution,[],[f228,f105])).
% 5.81/1.16  fof(f228,plain,(
% 5.81/1.16    ( ! [X0] : (r3_lattices(sK0,k5_lattices(sK0),k16_lattice3(sK0,X0)) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~r1_tarski(X0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0)) ) | ~spl9_9),
% 5.81/1.16    inference(superposition,[],[f82,f213])).
% 5.81/1.16  fof(f349,plain,(
% 5.81/1.16    ~spl9_12 | spl9_13 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7),
% 5.81/1.16    inference(avatar_split_clause,[],[f226,f175,f113,f108,f103,f98,f346,f342])).
% 5.81/1.16  fof(f342,plain,(
% 5.81/1.16    spl9_12 <=> r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,k5_lattices(sK0)))),
% 5.81/1.16    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 5.81/1.16  fof(f226,plain,(
% 5.81/1.16    r3_lattices(sK0,k5_lattices(sK0),k5_lattices(sK0)) | ~r1_tarski(a_2_3_lattice3(sK0,k5_lattices(sK0)),a_2_3_lattice3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_7)),
% 5.81/1.16    inference(superposition,[],[f221,f177])).
% 5.81/1.16  fof(f338,plain,(
% 5.81/1.16    spl9_11 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9),
% 5.81/1.16    inference(avatar_split_clause,[],[f329,f211,f183,f113,f108,f103,f98,f335])).
% 5.81/1.16  fof(f329,plain,(
% 5.81/1.16    r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.16    inference(subsumption_resolution,[],[f328,f100])).
% 5.81/1.16  fof(f328,plain,(
% 5.81/1.16    r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8 | ~spl9_9)),
% 5.81/1.16    inference(subsumption_resolution,[],[f327,f185])).
% 5.81/1.16  fof(f327,plain,(
% 5.81/1.16    r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_9)),
% 5.81/1.16    inference(subsumption_resolution,[],[f326,f115])).
% 5.81/1.16  fof(f326,plain,(
% 5.81/1.16    r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_9)),
% 5.81/1.16    inference(subsumption_resolution,[],[f325,f110])).
% 5.81/1.16  fof(f325,plain,(
% 5.81/1.16    r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_2 | ~spl9_9)),
% 5.81/1.16    inference(subsumption_resolution,[],[f323,f105])).
% 5.81/1.16  fof(f323,plain,(
% 5.81/1.16    r3_lattice3(sK0,k5_lattices(sK0),a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl9_9),
% 5.81/1.16    inference(superposition,[],[f94,f213])).
% 5.81/1.16  fof(f277,plain,(
% 5.81/1.16    ~spl9_6 | spl9_10 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 5.81/1.16    inference(avatar_split_clause,[],[f272,f113,f108,f103,f98,f274,f125])).
% 5.81/1.16  fof(f272,plain,(
% 5.81/1.16    sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) | ~v13_lattices(sK0) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.16    inference(subsumption_resolution,[],[f271,f100])).
% 5.81/1.16  fof(f271,plain,(
% 5.81/1.16    v2_struct_0(sK0) | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) | ~v13_lattices(sK0) | (~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.16    inference(subsumption_resolution,[],[f270,f115])).
% 5.81/1.16  fof(f270,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) | ~v13_lattices(sK0) | (~spl9_2 | ~spl9_3)),
% 5.81/1.16    inference(subsumption_resolution,[],[f269,f105])).
% 5.81/1.16  fof(f269,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | sK2(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0))) | ~v13_lattices(sK0) | ~spl9_3),
% 5.81/1.16    inference(resolution,[],[f168,f110])).
% 5.81/1.16  fof(f168,plain,(
% 5.81/1.16    ( ! [X3] : (~v4_lattice3(X3) | ~v10_lattices(X3) | ~l3_lattices(X3) | v2_struct_0(X3) | sK2(X3) = k15_lattice3(X3,a_2_3_lattice3(X3,sK2(X3))) | ~v13_lattices(X3)) )),
% 5.81/1.16    inference(subsumption_resolution,[],[f164,f50])).
% 5.81/1.16  fof(f164,plain,(
% 5.81/1.16    ( ! [X3] : (~v10_lattices(X3) | ~v4_lattice3(X3) | ~l3_lattices(X3) | v2_struct_0(X3) | sK2(X3) = k15_lattice3(X3,a_2_3_lattice3(X3,sK2(X3))) | ~l1_lattices(X3) | ~v13_lattices(X3)) )),
% 5.81/1.16    inference(duplicate_literal_removal,[],[f157])).
% 5.81/1.16  fof(f157,plain,(
% 5.81/1.16    ( ! [X3] : (~v10_lattices(X3) | ~v4_lattice3(X3) | ~l3_lattices(X3) | v2_struct_0(X3) | sK2(X3) = k15_lattice3(X3,a_2_3_lattice3(X3,sK2(X3))) | ~l1_lattices(X3) | v2_struct_0(X3) | ~v13_lattices(X3)) )),
% 5.81/1.16    inference(resolution,[],[f74,f69])).
% 5.81/1.16  fof(f214,plain,(
% 5.81/1.16    spl9_9 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8),
% 5.81/1.16    inference(avatar_split_clause,[],[f209,f183,f113,f108,f103,f98,f211])).
% 5.81/1.16  fof(f209,plain,(
% 5.81/1.16    k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8)),
% 5.81/1.16    inference(subsumption_resolution,[],[f208,f100])).
% 5.81/1.16  fof(f208,plain,(
% 5.81/1.16    v2_struct_0(sK0) | k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | (~spl9_2 | ~spl9_3 | ~spl9_4 | ~spl9_8)),
% 5.81/1.16    inference(subsumption_resolution,[],[f207,f115])).
% 5.81/1.16  fof(f207,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | (~spl9_2 | ~spl9_3 | ~spl9_8)),
% 5.81/1.16    inference(subsumption_resolution,[],[f206,f110])).
% 5.81/1.16  fof(f206,plain,(
% 5.81/1.16    ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | (~spl9_2 | ~spl9_8)),
% 5.81/1.16    inference(subsumption_resolution,[],[f196,f105])).
% 5.81/1.16  fof(f196,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~v4_lattice3(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = k16_lattice3(sK0,a_2_4_lattice3(sK0,k5_lattices(sK0))) | ~spl9_8),
% 5.81/1.16    inference(resolution,[],[f75,f185])).
% 5.81/1.16  fof(f186,plain,(
% 5.81/1.16    spl9_8 | spl9_1 | ~spl9_4 | ~spl9_7),
% 5.81/1.16    inference(avatar_split_clause,[],[f181,f175,f113,f98,f183])).
% 5.81/1.16  fof(f181,plain,(
% 5.81/1.16    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl9_1 | ~spl9_4 | ~spl9_7)),
% 5.81/1.16    inference(subsumption_resolution,[],[f180,f100])).
% 5.81/1.16  fof(f180,plain,(
% 5.81/1.16    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl9_4 | ~spl9_7)),
% 5.81/1.16    inference(subsumption_resolution,[],[f179,f115])).
% 5.81/1.16  fof(f179,plain,(
% 5.81/1.16    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl9_7),
% 5.81/1.16    inference(superposition,[],[f87,f177])).
% 5.81/1.16  fof(f178,plain,(
% 5.81/1.16    spl9_7 | spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 5.81/1.16    inference(avatar_split_clause,[],[f173,f113,f108,f103,f98,f175])).
% 5.81/1.16  fof(f173,plain,(
% 5.81/1.16    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | (spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.16    inference(subsumption_resolution,[],[f172,f100])).
% 5.81/1.16  fof(f172,plain,(
% 5.81/1.16    v2_struct_0(sK0) | k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | (~spl9_2 | ~spl9_3 | ~spl9_4)),
% 5.81/1.16    inference(subsumption_resolution,[],[f171,f115])).
% 5.81/1.16  fof(f171,plain,(
% 5.81/1.16    ~l3_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | (~spl9_2 | ~spl9_3)),
% 5.81/1.16    inference(subsumption_resolution,[],[f170,f105])).
% 5.81/1.16  fof(f170,plain,(
% 5.81/1.16    ~v10_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0) | k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~spl9_3),
% 5.81/1.16    inference(resolution,[],[f167,f110])).
% 5.81/1.16  fof(f167,plain,(
% 5.81/1.16    ( ! [X0] : (~v4_lattice3(X0) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k5_lattices(X0) = k15_lattice3(X0,a_2_3_lattice3(X0,k5_lattices(X0)))) )),
% 5.81/1.16    inference(subsumption_resolution,[],[f166,f50])).
% 5.81/1.16  fof(f166,plain,(
% 5.81/1.16    ( ! [X0] : (~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k5_lattices(X0) = k15_lattice3(X0,a_2_3_lattice3(X0,k5_lattices(X0))) | ~l1_lattices(X0)) )),
% 5.81/1.16    inference(duplicate_literal_removal,[],[f155])).
% 5.81/1.16  fof(f155,plain,(
% 5.81/1.16    ( ! [X0] : (~v10_lattices(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | k5_lattices(X0) = k15_lattice3(X0,a_2_3_lattice3(X0,k5_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.81/1.16    inference(resolution,[],[f74,f60])).
% 5.81/1.16  fof(f128,plain,(
% 5.81/1.16    ~spl9_5 | ~spl9_6 | spl9_1 | ~spl9_2 | ~spl9_4),
% 5.81/1.16    inference(avatar_split_clause,[],[f119,f113,f103,f98,f125,f121])).
% 5.81/1.16  fof(f119,plain,(
% 5.81/1.16    ~v13_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | (spl9_1 | ~spl9_2 | ~spl9_4)),
% 5.81/1.16    inference(subsumption_resolution,[],[f118,f115])).
% 5.81/1.17  fof(f118,plain,(
% 5.81/1.17    ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | (spl9_1 | ~spl9_2)),
% 5.81/1.17    inference(subsumption_resolution,[],[f117,f105])).
% 5.81/1.17  fof(f117,plain,(
% 5.81/1.17    ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl9_1),
% 5.81/1.17    inference(subsumption_resolution,[],[f44,f100])).
% 5.81/1.17  fof(f44,plain,(
% 5.81/1.17    v2_struct_0(sK0) | ~v10_lattices(sK0) | ~v13_lattices(sK0) | ~l3_lattices(sK0) | k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)),
% 5.81/1.17    inference(cnf_transformation,[],[f18])).
% 5.81/1.17  fof(f18,plain,(
% 5.81/1.17    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 5.81/1.17    inference(flattening,[],[f17])).
% 5.81/1.17  fof(f17,plain,(
% 5.81/1.17    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 5.81/1.17    inference(ennf_transformation,[],[f16])).
% 5.81/1.17  fof(f16,negated_conjecture,(
% 5.81/1.17    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 5.81/1.17    inference(negated_conjecture,[],[f15])).
% 5.81/1.17  fof(f15,conjecture,(
% 5.81/1.17    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 5.81/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 5.81/1.17  fof(f116,plain,(
% 5.81/1.17    spl9_4),
% 5.81/1.17    inference(avatar_split_clause,[],[f48,f113])).
% 5.81/1.17  fof(f48,plain,(
% 5.81/1.17    l3_lattices(sK0)),
% 5.81/1.17    inference(cnf_transformation,[],[f18])).
% 5.81/1.17  fof(f111,plain,(
% 5.81/1.17    spl9_3),
% 5.81/1.17    inference(avatar_split_clause,[],[f47,f108])).
% 5.81/1.17  fof(f47,plain,(
% 5.81/1.17    v4_lattice3(sK0)),
% 5.81/1.17    inference(cnf_transformation,[],[f18])).
% 5.81/1.17  fof(f106,plain,(
% 5.81/1.17    spl9_2),
% 5.81/1.17    inference(avatar_split_clause,[],[f46,f103])).
% 5.81/1.17  fof(f46,plain,(
% 5.81/1.17    v10_lattices(sK0)),
% 5.81/1.17    inference(cnf_transformation,[],[f18])).
% 5.81/1.17  fof(f101,plain,(
% 5.81/1.17    ~spl9_1),
% 5.81/1.17    inference(avatar_split_clause,[],[f45,f98])).
% 5.81/1.17  fof(f45,plain,(
% 5.81/1.17    ~v2_struct_0(sK0)),
% 5.81/1.17    inference(cnf_transformation,[],[f18])).
% 5.81/1.17  % SZS output end Proof for theBenchmark
% 5.81/1.17  % (28826)------------------------------
% 5.81/1.17  % (28826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.81/1.17  % (28826)Termination reason: Refutation
% 5.81/1.17  
% 5.81/1.17  % (28826)Memory used [KB]: 6268
% 5.81/1.17  % (28826)Time elapsed: 0.718 s
% 5.81/1.17  % (28826)------------------------------
% 5.81/1.17  % (28826)------------------------------
% 5.81/1.18  % (28800)Success in time 0.8 s
%------------------------------------------------------------------------------
