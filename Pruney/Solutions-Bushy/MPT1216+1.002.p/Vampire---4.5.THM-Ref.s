%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1216+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:29 EST 2020

% Result     : Theorem 7.02s
% Output     : Refutation 7.50s
% Verified   : 
% Statistics : Number of formulae       :  446 (4774 expanded)
%              Number of leaves         :   63 (1780 expanded)
%              Depth                    :   22
%              Number of atoms          : 2837 (19629 expanded)
%              Number of equality atoms :  257 (1558 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10978,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f123,f128,f133,f138,f143,f150,f159,f174,f179,f180,f185,f190,f197,f220,f234,f245,f250,f255,f352,f357,f823,f828,f833,f838,f843,f848,f1241,f1246,f3489,f3494,f3499,f3546,f3551,f3556,f3561,f3566,f3571,f3576,f3581,f7880,f9944,f10972,f10977])).

fof(f10977,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | spl8_30
    | ~ spl8_33
    | ~ spl8_35 ),
    inference(avatar_contradiction_clause,[],[f10976])).

fof(f10976,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | spl8_30
    | ~ spl8_33
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f10975,f10866])).

fof(f10866,plain,
    ( k7_lattices(sK0,sK2) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_33
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f4523,f10853])).

fof(f10853,plain,
    ( sK1 = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_33
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f10256,f10513])).

fof(f10513,plain,
    ( sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_9
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f10182,f169])).

fof(f169,plain,
    ( k4_lattices(sK0,sK1,sK2) = k5_lattices(sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl8_9
  <=> k4_lattices(sK0,sK1,sK2) = k5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f10182,plain,
    ( sK1 = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f7867,f7166])).

fof(f7166,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f5498,f7129])).

fof(f7129,plain,
    ( sK1 = k4_lattices(sK0,sK1,sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f5113,f6195])).

fof(f6195,plain,
    ( sK1 = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f5464,f2609])).

fof(f2609,plain,
    ( sK1 = k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f753,f2605])).

fof(f2605,plain,
    ( sK1 = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2375,f2573])).

fof(f2573,plain,
    ( sK1 = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2387,f850])).

fof(f850,plain,
    ( sK1 = k4_lattices(sK0,k6_lattices(sK0),sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f142,f822,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,k6_lattices(X0),X1) = X1
      | ~ v10_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,k6_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v14_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,k6_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattices)).

fof(f822,plain,
    ( v14_lattices(sK0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f820])).

fof(f820,plain,
    ( spl8_22
  <=> v14_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f142,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f132,plain,
    ( l3_lattices(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f122,plain,
    ( v10_lattices(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f117,plain,
    ( ~ v2_struct_0(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f2387,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f142,f1245,f229])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f228,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f111,f84])).

fof(f84,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
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
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f1245,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f1243])).

fof(f1243,plain,
    ( spl8_29
  <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f2375,plain,
    ( k2_lattices(sK0,sK1,k6_lattices(sK0)) = k4_lattices(sK0,sK1,k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f142,f1245,f226])).

fof(f226,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f225,f75])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f110,f84])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f753,plain,
    ( k2_lattices(sK0,sK1,k6_lattices(sK0)) = k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f752,f658])).

fof(f658,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f601,f203])).

fof(f203,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f127,f142,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ v10_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_lattices(X0) = k3_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattices)).

fof(f127,plain,
    ( v17_lattices(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_3
  <=> v17_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f601,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f117,f158,f196,f142,f356,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f356,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl8_21
  <=> m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f196,plain,
    ( v4_lattices(sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl8_14
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f158,plain,
    ( l2_lattices(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl8_8
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f752,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)) = k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f751,f645])).

fof(f645,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f613,f640])).

fof(f640,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f621,f205])).

fof(f205,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f127,f142,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
      | ~ v10_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k7_lattices(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_lattices)).

fof(f621,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f117,f233,f149,f142,f356,f111])).

fof(f149,plain,
    ( l1_lattices(sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_7
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f233,plain,
    ( v6_lattices(sK0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl8_16
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f613,plain,
    ( k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f117,f233,f149,f142,f356,f110])).

fof(f751,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f556,f303])).

fof(f303,plain,
    ( k2_lattices(sK0,sK1,sK1) = k4_lattices(sK0,sK1,sK1)
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f117,f149,f142,f142,f233,f110])).

fof(f556,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,sK1),sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)),k2_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_11
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f117,f132,f178,f142,f142,f356,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v11_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v11_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ! [X3] :
                    ( k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v11_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_lattices)).

fof(f178,plain,
    ( v11_lattices(sK0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl8_11
  <=> v11_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f5464,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK1)) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_28
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f1240,f3555,f223])).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f222,f76])).

fof(f76,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f107,f82])).

fof(f82,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3555,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f3553])).

fof(f3553,plain,
    ( spl8_35
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f1240,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f1238])).

fof(f1238,plain,
    ( spl8_28
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f5113,plain,
    ( k4_lattices(sK0,sK1,sK1) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_27
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f847,f3555,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k5_lattices(X0),X1) = X1
      | ~ v10_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

fof(f847,plain,
    ( v13_lattices(sK0)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f845])).

fof(f845,plain,
    ( spl8_27
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f5498,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f351,f3555,f229])).

fof(f351,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl8_20
  <=> m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f7867,plain,
    ( sK1 = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k4_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f7339,f298])).

fof(f298,plain,
    ( k4_lattices(sK0,sK1,sK2) = k4_lattices(sK0,sK2,sK1)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f117,f149,f137,f142,f233,f111])).

fof(f137,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f7339,plain,
    ( sK1 = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k4_lattices(sK0,sK2,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f7088,f7129])).

fof(f7088,plain,
    ( k4_lattices(sK0,sK1,sK1) = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1)),k4_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK1)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_22
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f6127,f5114])).

fof(f5114,plain,
    ( k4_lattices(sK0,sK1,sK1) = k4_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_22
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f822,f3555,f90])).

fof(f6127,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,sK1)) = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1)),k4_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK1)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f6103,f6108])).

fof(f6108,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,sK1)) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f5473,f5497])).

fof(f5497,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),k4_lattices(sK0,sK1,sK1)) = k4_lattices(sK0,k4_lattices(sK0,sK1,sK1),k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f1245,f3555,f229])).

fof(f5473,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k6_lattices(sK0)) = k4_lattices(sK0,k4_lattices(sK0,sK1,sK1),k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f1245,f3555,f226])).

fof(f6103,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k6_lattices(sK0)) = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1)),k4_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK1)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f6052,f6092])).

fof(f6092,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f5474,f5498])).

fof(f5474,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f351,f3555,f226])).

fof(f6052,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k6_lattices(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK2)),k4_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK1)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f5890,f6042])).

fof(f6042,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2) = k4_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f5477,f5501])).

fof(f5501,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2) = k4_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f137,f3555,f229])).

fof(f5477,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2) = k4_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f137,f3555,f226])).

fof(f5890,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k6_lattices(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK2)),k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f5541,f445])).

fof(f445,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f400,f202])).

fof(f202,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f127,f137,f91])).

fof(f400,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k1_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f158,f196,f137,f351,f107])).

fof(f5541,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k1_lattices(sK0,k7_lattices(sK0,sK2),sK2)) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK2)),k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f127,f137,f351,f3555,f240])).

fof(f240,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v17_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X1,k1_lattices(X0,X2,X3)) = k1_lattices(X0,k2_lattices(X0,X1,X2),k2_lattices(X0,X1,X3))
      | v2_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f96,f79])).

fof(f79,plain,(
    ! [X0] :
      ( v11_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v16_lattices(X0)
        & v15_lattices(X0)
        & v11_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v17_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v17_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v16_lattices(X0)
          & v15_lattices(X0)
          & v11_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_lattices)).

fof(f10256,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_33
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f10186,f10251])).

fof(f10251,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_33
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f10158,f4219])).

fof(f4219,plain,
    ( k2_lattices(sK0,sK1,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_33 ),
    inference(backward_demodulation,[],[f704,f3884])).

fof(f3884,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f351,f3545,f226])).

fof(f3545,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f3543])).

fof(f3543,plain,
    ( spl8_33
  <=> m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f704,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK1,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f703,f524])).

fof(f524,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f523,f271])).

fof(f271,plain,
    ( k1_lattices(sK0,sK1,sK2) = k3_lattices(sK0,sK1,sK2)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f117,f158,f137,f142,f196,f107])).

fof(f523,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f522,f437])).

fof(f437,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f408,f417])).

fof(f417,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f233,f149,f142,f351,f111])).

fof(f408,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f149,f233,f142,f351,f110])).

fof(f522,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),sK1),k5_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f363,f439])).

fof(f439,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f407,f204])).

fof(f204,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f127,f137,f92])).

fof(f407,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k2_lattices(sK0,k7_lattices(sK0,sK2),sK2)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f149,f233,f137,f351,f110])).

fof(f363,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),sK1),k2_lattices(sK0,k7_lattices(sK0,sK2),sK2))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f132,f178,f137,f142,f351,f96])).

fof(f703,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) = k2_lattices(sK0,sK1,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f702,f662])).

fof(f662,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(backward_demodulation,[],[f606,f598])).

fof(f598,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f117,f196,f158,f351,f356,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_lattices)).

fof(f606,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)) = k3_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f117,f196,f158,f351,f356,f107])).

fof(f702,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) = k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f701,f411])).

fof(f411,plain,
    ( k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f233,f149,f142,f351,f110])).

fof(f701,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f573,f645])).

fof(f573,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k2_lattices(sK0,sK1,k7_lattices(sK0,sK1)))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_11
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f117,f132,f178,f351,f142,f356,f96])).

fof(f10158,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)) = k2_lattices(sK0,sK1,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f7580,f10122])).

fof(f10122,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)) = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k5_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f7273,f275])).

fof(f275,plain,
    ( k3_lattices(sK0,sK2,sK1) = k3_lattices(sK0,sK1,sK2)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f117,f158,f137,f142,f196,f106])).

fof(f7273,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK2,sK1)) = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k5_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f6252,f7129])).

fof(f6252,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1)),k5_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK1)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f6208,f5453])).

fof(f5453,plain,
    ( k3_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2) = k3_lattices(sK0,sK2,k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f137,f3555,f215])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f214,f76])).

fof(f214,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f106,f82])).

fof(f6208,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1)),k5_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f5975,f5461])).

fof(f5461,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2) = k3_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f137,f3555,f223])).

fof(f5975,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2)) = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1)),k5_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f5784,f5482])).

fof(f5482,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f351,f3555,f226])).

fof(f5784,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2)) = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1)),k5_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f5626,f439])).

fof(f5626,plain,
    ( k2_lattices(sK0,k7_lattices(sK0,sK2),k1_lattices(sK0,k4_lattices(sK0,sK1,sK1),sK2)) = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1)),k2_lattices(sK0,k7_lattices(sK0,sK2),sK2))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_20
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f127,f351,f137,f3555,f240])).

fof(f7580,plain,
    ( k2_lattices(sK0,sK1,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k5_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f7211,f842])).

fof(f842,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f840])).

fof(f840,plain,
    ( spl8_26
  <=> k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f7211,plain,
    ( k2_lattices(sK0,sK1,k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),sK1),k4_lattices(sK0,k7_lattices(sK0,sK1),sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f6107,f7129])).

fof(f6107,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k4_lattices(sK0,sK1,sK1)),k4_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,sK1)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f6082,f6092])).

fof(f6082,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2))) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK2)),k4_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,sK1)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f5892,f6076])).

fof(f6076,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_21
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f5475,f5499])).

fof(f5499,plain,
    ( k4_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK1)) = k4_lattices(sK0,k7_lattices(sK0,sK1),k4_lattices(sK0,sK1,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_21
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f356,f3555,f229])).

fof(f5475,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK1)) = k4_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_21
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f356,f3555,f226])).

fof(f5892,plain,
    ( k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK2)),k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK1))) = k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k3_lattices(sK0,k7_lattices(sK0,sK1),k7_lattices(sK0,sK2)))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f5539,f662])).

fof(f5539,plain,
    ( k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k1_lattices(sK0,k7_lattices(sK0,sK2),k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK2)),k2_lattices(sK0,k4_lattices(sK0,sK1,sK1),k7_lattices(sK0,sK1)))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f132,f117,f127,f356,f351,f3555,f240])).

fof(f10186,plain,
    ( k1_lattices(sK0,k4_lattices(sK0,sK1,k7_lattices(sK0,sK2)),k5_lattices(sK0)) = k2_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f10122,f7166])).

fof(f4523,plain,
    ( k7_lattices(sK0,sK2) = k1_lattices(sK0,k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2)),k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_33 ),
    inference(forward_demodulation,[],[f3835,f4310])).

fof(f4310,plain,
    ( k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_33 ),
    inference(forward_demodulation,[],[f3877,f3898])).

fof(f3898,plain,
    ( k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k7_lattices(sK0,sK2),k3_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f351,f3545,f229])).

fof(f3877,plain,
    ( k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)) = k4_lattices(sK0,k3_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f351,f3545,f226])).

fof(f3835,plain,
    ( k7_lattices(sK0,sK2) = k1_lattices(sK0,k2_lattices(sK0,k3_lattices(sK0,sK1,sK2),k7_lattices(sK0,sK2)),k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f351,f3545,f212])).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f211])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | v2_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f103,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(f10975,plain,
    ( k7_lattices(sK0,sK2) != k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_20
    | spl8_30 ),
    inference(unit_resulting_resolution,[],[f158,f117,f142,f351,f3487,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_lattices(X0,X1,X2) != X2
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f3487,plain,
    ( ~ r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_30 ),
    inference(avatar_component_clause,[],[f3486])).

fof(f3486,plain,
    ( spl8_30
  <=> r1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f10972,plain,
    ( ~ spl8_30
    | spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | spl8_10
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f10966,f349,f252,f247,f231,f171,f140,f130,f115,f3486])).

fof(f171,plain,
    ( spl8_10
  <=> r3_lattices(sK0,sK1,k7_lattices(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f247,plain,
    ( spl8_18
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f252,plain,
    ( spl8_19
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f10966,plain,
    ( ~ r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | spl8_10
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f249,f233,f254,f132,f142,f351,f172,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f172,plain,
    ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f171])).

fof(f254,plain,
    ( v9_lattices(sK0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f252])).

fof(f249,plain,
    ( v8_lattices(sK0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f247])).

fof(f9944,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_30
    | ~ spl8_36 ),
    inference(avatar_contradiction_clause,[],[f9943])).

fof(f9943,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_9
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_30
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f9942,f168])).

fof(f168,plain,
    ( k4_lattices(sK0,sK1,sK2) != k5_lattices(sK0)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f167])).

fof(f9942,plain,
    ( k4_lattices(sK0,sK1,sK2) = k5_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_30
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f7887,f8993])).

fof(f8993,plain,
    ( k5_lattices(sK0) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_28
    | ~ spl8_30
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f8238,f3522])).

fof(f3522,plain,
    ( k5_lattices(sK0) = k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f3511,f435])).

fof(f435,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f410,f431])).

fof(f431,plain,
    ( k5_lattices(sK0) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f416,f204])).

fof(f416,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f233,f149,f137,f351,f111])).

fof(f410,plain,
    ( k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k4_lattices(sK0,sK2,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f233,f149,f137,f351,f110])).

fof(f3511,plain,
    ( k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)) = k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20
    | ~ spl8_30 ),
    inference(backward_demodulation,[],[f503,f3503])).

fof(f3503,plain,
    ( k7_lattices(sK0,sK2) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20
    | ~ spl8_30 ),
    inference(backward_demodulation,[],[f404,f3501])).

fof(f3501,plain,
    ( k7_lattices(sK0,sK2) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_20
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f117,f158,f142,f351,f3488,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3488,plain,
    ( r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f3486])).

fof(f404,plain,
    ( k1_lattices(sK0,sK1,k7_lattices(sK0,sK2)) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f196,f158,f142,f351,f107])).

fof(f503,plain,
    ( k2_lattices(sK0,sK2,k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))) = k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f502,f448])).

fof(f448,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f401,f398])).

fof(f398,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f196,f158,f142,f351,f106])).

fof(f401,plain,
    ( k1_lattices(sK0,k7_lattices(sK0,sK2),sK1) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK1)
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f158,f196,f142,f351,f107])).

fof(f502,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f501,f435])).

fof(f501,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k4_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_16
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f370,f326])).

fof(f326,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK2,sK1)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f301,f298])).

fof(f301,plain,
    ( k2_lattices(sK0,sK2,sK1) = k4_lattices(sK0,sK2,sK1)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f117,f149,f142,f137,f233,f110])).

fof(f370,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,k7_lattices(sK0,sK2),sK1)) = k1_lattices(sK0,k2_lattices(sK0,sK2,k7_lattices(sK0,sK2)),k2_lattices(sK0,sK2,sK1))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f132,f178,f142,f137,f351,f96])).

fof(f8238,plain,
    ( k1_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2)) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_28
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f1240,f3560,f223])).

fof(f3560,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f3558])).

fof(f3558,plain,
    ( spl8_36
  <=> m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f7887,plain,
    ( k4_lattices(sK0,sK1,sK2) = k3_lattices(sK0,k5_lattices(sK0),k4_lattices(sK0,sK1,sK2))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_27
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f847,f3560,f89])).

fof(f7880,plain,
    ( spl8_41
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f7130,f3553,f1243,f1238,f845,f820,f354,f231,f194,f176,f156,f147,f140,f130,f125,f120,f115,f7877])).

fof(f7877,plain,
    ( spl8_41
  <=> sK1 = k2_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f7130,plain,
    ( sK1 = k2_lattices(sK0,sK1,sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_11
    | ~ spl8_14
    | ~ spl8_16
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f303,f7129])).

fof(f3581,plain,
    ( spl8_40
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f675,f354,f247,f231,f147,f140,f130,f125,f120,f115,f3578])).

fof(f3578,plain,
    ( spl8_40
  <=> sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f675,plain,
    ( sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f584,f649])).

fof(f649,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f609,f205])).

fof(f609,plain,
    ( k4_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k2_lattices(sK0,k7_lattices(sK0,sK1),sK1)
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f117,f149,f233,f142,f356,f110])).

fof(f584,plain,
    ( sK1 = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK1),sK1),sK1)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_18
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f117,f132,f249,f142,f356,f103])).

fof(f3576,plain,
    ( spl8_39
    | spl8_1
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f3536,f3496,f156,f135,f115,f3573])).

fof(f3573,plain,
    ( spl8_39
  <=> r1_lattices(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f3496,plain,
    ( spl8_32
  <=> sK2 = k1_lattices(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f3536,plain,
    ( r1_lattices(sK0,sK2,sK2)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f158,f117,f137,f137,f3498,f94])).

fof(f3498,plain,
    ( sK2 = k1_lattices(sK0,sK2,sK2)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f3496])).

fof(f3571,plain,
    ( spl8_38
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f458,f349,f247,f231,f147,f135,f130,f125,f120,f115,f3568])).

fof(f3568,plain,
    ( spl8_38
  <=> sK2 = k1_lattices(sK0,k5_lattices(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f458,plain,
    ( sK2 = k1_lattices(sK0,k5_lattices(sK0),sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f387,f439])).

fof(f387,plain,
    ( sK2 = k1_lattices(sK0,k2_lattices(sK0,k7_lattices(sK0,sK2),sK2),sK2)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_18
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f117,f132,f249,f137,f351,f103])).

fof(f3566,plain,
    ( spl8_37
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f321,f231,f147,f135,f115,f3563])).

fof(f3563,plain,
    ( spl8_37
  <=> m1_subset_1(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f321,plain,
    ( m1_subset_1(k4_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f198,f300])).

fof(f300,plain,
    ( k2_lattices(sK0,sK2,sK2) = k4_lattices(sK0,sK2,sK2)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f117,f149,f137,f137,f233,f110])).

fof(f198,plain,
    ( m1_subset_1(k2_lattices(sK0,sK2,sK2),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f117,f149,f137,f137,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattices)).

fof(f3561,plain,
    ( spl8_36
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f313,f231,f147,f140,f135,f115,f3558])).

fof(f313,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f200,f302])).

fof(f302,plain,
    ( k4_lattices(sK0,sK1,sK2) = k2_lattices(sK0,sK1,sK2)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f117,f149,f137,f142,f233,f110])).

fof(f200,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f117,f149,f137,f142,f112])).

fof(f3556,plain,
    ( spl8_35
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f309,f231,f147,f140,f115,f3553])).

fof(f309,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f201,f303])).

fof(f201,plain,
    ( m1_subset_1(k2_lattices(sK0,sK1,sK1),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f117,f149,f142,f142,f112])).

fof(f3551,plain,
    ( spl8_34
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f3530,f3491,f156,f140,f115,f3548])).

fof(f3548,plain,
    ( spl8_34
  <=> r1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f3491,plain,
    ( spl8_31
  <=> sK1 = k1_lattices(sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f3530,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_31 ),
    inference(unit_resulting_resolution,[],[f158,f117,f142,f142,f3493,f94])).

fof(f3493,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f3491])).

fof(f3546,plain,
    ( spl8_33
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f284,f194,f156,f140,f135,f115,f3543])).

fof(f284,plain,
    ( m1_subset_1(k3_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(backward_demodulation,[],[f208,f271])).

fof(f208,plain,
    ( m1_subset_1(k1_lattices(sK0,sK1,sK2),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f117,f137,f142,f158,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_lattices)).

fof(f3499,plain,
    ( spl8_32
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f3014,f1243,f820,f354,f194,f156,f140,f135,f130,f125,f120,f115,f3496])).

fof(f3014,plain,
    ( sK2 = k1_lattices(sK0,sK2,sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f269,f3013])).

fof(f3013,plain,
    ( sK2 = k3_lattices(sK0,sK2,sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2973,f2582])).

fof(f2582,plain,
    ( sK2 = k2_lattices(sK0,sK2,k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2376,f2572])).

fof(f2572,plain,
    ( sK2 = k4_lattices(sK0,sK2,k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2388,f849])).

fof(f849,plain,
    ( sK2 = k4_lattices(sK0,k6_lattices(sK0),sK2)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f137,f822,f90])).

fof(f2388,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK2) = k4_lattices(sK0,sK2,k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f137,f1245,f229])).

fof(f2376,plain,
    ( k2_lattices(sK0,sK2,k6_lattices(sK0)) = k4_lattices(sK0,sK2,k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f137,f1245,f226])).

fof(f2973,plain,
    ( k3_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f2837,f2967])).

fof(f2967,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f2360,f2966])).

fof(f2966,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2336,f2763])).

fof(f2763,plain,
    ( k6_lattices(sK0) = k2_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f2372,f2762])).

fof(f2762,plain,
    ( k6_lattices(sK0) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2756,f665])).

fof(f665,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21 ),
    inference(backward_demodulation,[],[f605,f663])).

fof(f663,plain,
    ( k6_lattices(sK0) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f597,f203])).

fof(f597,plain,
    ( k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f117,f196,f158,f142,f356,f106])).

fof(f605,plain,
    ( k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) = k3_lattices(sK0,sK1,k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f117,f196,f158,f142,f356,f107])).

fof(f2756,plain,
    ( k1_lattices(sK0,sK1,k7_lattices(sK0,sK1)) = k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f2738,f2746])).

fof(f2746,plain,
    ( k7_lattices(sK0,sK1) = k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2368,f852])).

fof(f852,plain,
    ( k7_lattices(sK0,sK1) = k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f356,f822,f90])).

fof(f2368,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)) = k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_21
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f356,f1245,f226])).

fof(f2738,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) = k1_lattices(sK0,sK1,k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f2686,f2730])).

fof(f2730,plain,
    ( sK1 = k2_lattices(sK0,k6_lattices(sK0),sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2369,f850])).

fof(f2369,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),sK1) = k2_lattices(sK0,k6_lattices(sK0),sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f142,f1245,f226])).

fof(f2686,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f2554,f2372])).

fof(f2554,plain,
    ( k2_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) = k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2416,f665])).

fof(f2416,plain,
    ( k2_lattices(sK0,k6_lattices(sK0),k1_lattices(sK0,sK1,k7_lattices(sK0,sK1))) = k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),sK1),k2_lattices(sK0,k6_lattices(sK0),k7_lattices(sK0,sK1)))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_21
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f127,f356,f142,f1245,f240])).

fof(f2372,plain,
    ( k4_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) = k2_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f1245,f1245,f226])).

fof(f2336,plain,
    ( k6_lattices(sK0) = k1_lattices(sK0,k2_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)),k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f1245,f1245,f212])).

fof(f2360,plain,
    ( k1_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)) = k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f122,f1245,f1245,f223])).

fof(f2837,plain,
    ( k3_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f2598,f2360])).

fof(f2598,plain,
    ( k3_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,k1_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2587,f269])).

fof(f2587,plain,
    ( k1_lattices(sK0,sK2,sK2) = k2_lattices(sK0,sK2,k1_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f2472,f2582])).

fof(f2472,plain,
    ( k2_lattices(sK0,sK2,k1_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK2,k6_lattices(sK0)),k2_lattices(sK0,sK2,k6_lattices(sK0)))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f127,f137,f1245,f1245,f240])).

fof(f269,plain,
    ( k1_lattices(sK0,sK2,sK2) = k3_lattices(sK0,sK2,sK2)
    | spl8_1
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f117,f158,f137,f137,f196,f107])).

fof(f3494,plain,
    ( spl8_31
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f3002,f1243,f820,f354,f194,f156,f140,f130,f125,f120,f115,f3491])).

fof(f3002,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f272,f3001])).

fof(f3001,plain,
    ( sK1 = k3_lattices(sK0,sK1,sK1)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2972,f2605])).

fof(f2972,plain,
    ( k3_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,k6_lattices(sK0))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f2836,f2967])).

fof(f2836,plain,
    ( k3_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,k3_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f2621,f2360])).

fof(f2621,plain,
    ( k3_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2610,f272])).

fof(f2610,plain,
    ( k1_lattices(sK0,sK1,sK1) = k2_lattices(sK0,sK1,k1_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0)))
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f2471,f2605])).

fof(f2471,plain,
    ( k2_lattices(sK0,sK1,k1_lattices(sK0,k6_lattices(sK0),k6_lattices(sK0))) = k1_lattices(sK0,k2_lattices(sK0,sK1,k6_lattices(sK0)),k2_lattices(sK0,sK1,k6_lattices(sK0)))
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f132,f117,f127,f142,f1245,f1245,f240])).

fof(f272,plain,
    ( k1_lattices(sK0,sK1,sK1) = k3_lattices(sK0,sK1,sK1)
    | spl8_1
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f117,f158,f142,f142,f196,f107])).

fof(f3489,plain,
    ( spl8_30
    | spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f406,f349,f252,f247,f231,f171,f140,f130,f115,f3486])).

fof(f406,plain,
    ( r1_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f249,f233,f254,f117,f132,f142,f173,f351,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f173,plain,
    ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f171])).

fof(f1246,plain,
    ( spl8_29
    | spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f210,f156,f115,f1243])).

fof(f210,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f117,f158,f93])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_lattices)).

fof(f1241,plain,
    ( spl8_28
    | spl8_1
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f165,f147,f115,f1238])).

fof(f165,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_7 ),
    inference(unit_resulting_resolution,[],[f117,f149,f88])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f848,plain,
    ( spl8_27
    | spl8_1
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f268,f182,f130,f115,f845])).

fof(f182,plain,
    ( spl8_12
  <=> v15_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f268,plain,
    ( v13_lattices(sK0)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f132,f117,f184,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v13_lattices(X0)
      | v2_struct_0(X0)
      | ~ v15_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
        & v13_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v15_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v14_lattices(X0)
          & v13_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_lattices)).

fof(f184,plain,
    ( v15_lattices(sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f182])).

fof(f843,plain,
    ( spl8_26
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f205,f140,f130,f125,f120,f115,f840])).

fof(f838,plain,
    ( spl8_25
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f204,f135,f130,f125,f120,f115,f835])).

fof(f835,plain,
    ( spl8_25
  <=> k5_lattices(sK0) = k4_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f833,plain,
    ( spl8_24
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f203,f140,f130,f125,f120,f115,f830])).

fof(f830,plain,
    ( spl8_24
  <=> k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f828,plain,
    ( spl8_23
    | spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f202,f135,f130,f125,f120,f115,f825])).

fof(f825,plain,
    ( spl8_23
  <=> k6_lattices(sK0) = k3_lattices(sK0,k7_lattices(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f823,plain,
    ( spl8_22
    | spl8_1
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f267,f182,f130,f115,f820])).

fof(f267,plain,
    ( v14_lattices(sK0)
    | spl8_1
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f132,f117,f184,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v14_lattices(X0)
      | v2_struct_0(X0)
      | ~ v15_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f357,plain,
    ( spl8_21
    | spl8_1
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f192,f140,f130,f115,f354])).

fof(f192,plain,
    ( m1_subset_1(k7_lattices(sK0,sK1),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f117,f132,f142,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f352,plain,
    ( spl8_20
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f191,f135,f130,f115,f349])).

fof(f191,plain,
    ( m1_subset_1(k7_lattices(sK0,sK2),u1_struct_0(sK0))
    | spl8_1
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f117,f132,f137,f105])).

fof(f255,plain,
    ( spl8_19
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f164,f130,f120,f115,f252])).

fof(f164,plain,
    ( v9_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f122,f117,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f250,plain,
    ( spl8_18
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f163,f130,f120,f115,f247])).

fof(f163,plain,
    ( v8_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f122,f117,f86])).

fof(f245,plain,
    ( spl8_17
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f162,f130,f120,f115,f242])).

fof(f242,plain,
    ( spl8_17
  <=> v7_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f162,plain,
    ( v7_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f122,f117,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f234,plain,
    ( spl8_16
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f161,f130,f120,f115,f231])).

fof(f161,plain,
    ( v6_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f122,f117,f84])).

fof(f220,plain,
    ( spl8_15
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f160,f130,f120,f115,f217])).

fof(f217,plain,
    ( spl8_15
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f160,plain,
    ( v5_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f122,f117,f83])).

fof(f83,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f197,plain,
    ( spl8_14
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f154,f130,f120,f115,f194])).

fof(f154,plain,
    ( v4_lattices(sK0)
    | spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f122,f117,f82])).

fof(f190,plain,
    ( spl8_13
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f153,f130,f125,f115,f187])).

fof(f187,plain,
    ( spl8_13
  <=> v16_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f153,plain,
    ( v16_lattices(sK0)
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f127,f117,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v16_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f185,plain,
    ( spl8_12
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f152,f130,f125,f115,f182])).

fof(f152,plain,
    ( v15_lattices(sK0)
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f127,f117,f80])).

fof(f80,plain,(
    ! [X0] :
      ( v15_lattices(X0)
      | v2_struct_0(X0)
      | ~ v17_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f180,plain,
    ( ~ spl8_9
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f68,f171,f167])).

fof(f68,plain,
    ( ~ r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k4_lattices(sK0,sK1,sK2) != k5_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <~> r3_lattices(X0,X1,k7_lattices(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v17_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v17_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
                <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k4_lattices(X0,X1,X2) = k5_lattices(X0)
              <=> r3_lattices(X0,X1,k7_lattices(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_lattices)).

fof(f179,plain,
    ( spl8_11
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f151,f130,f125,f115,f176])).

fof(f151,plain,
    ( v11_lattices(sK0)
    | spl8_1
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f127,f117,f79])).

fof(f174,plain,
    ( spl8_9
    | spl8_10 ),
    inference(avatar_split_clause,[],[f67,f171,f167])).

fof(f67,plain,
    ( r3_lattices(sK0,sK1,k7_lattices(sK0,sK2))
    | k4_lattices(sK0,sK1,sK2) = k5_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f159,plain,
    ( spl8_8
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f145,f130,f156])).

fof(f145,plain,
    ( l2_lattices(sK0)
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f76])).

fof(f150,plain,
    ( spl8_7
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f144,f130,f147])).

fof(f144,plain,
    ( l1_lattices(sK0)
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f132,f75])).

fof(f143,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f70,f140])).

fof(f70,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f138,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f69,f135])).

fof(f69,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f133,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f74,f130])).

fof(f74,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f128,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f73,f125])).

fof(f73,plain,(
    v17_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f123,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f72,f120])).

fof(f72,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f118,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f71,f115])).

fof(f71,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

%------------------------------------------------------------------------------
