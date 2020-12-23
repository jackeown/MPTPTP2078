%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t33_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:55 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 497 expanded)
%              Number of leaves         :   29 ( 188 expanded)
%              Depth                    :   16
%              Number of atoms          : 1005 (2385 expanded)
%              Number of equality atoms :   22 (  61 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2622,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f98,f102,f111,f115,f133,f141,f223,f258,f506,f555,f765,f862,f881,f885,f1379,f1383,f1490,f1494,f2438,f2468,f2585,f2613,f2621])).

fof(f2621,plain,
    ( ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | spl13_13
    | ~ spl13_46
    | ~ spl13_80
    | ~ spl13_86
    | ~ spl13_92
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f2620])).

fof(f2620,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_13
    | ~ spl13_46
    | ~ spl13_80
    | ~ spl13_86
    | ~ spl13_92
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f2535,f2619])).

fof(f2619,plain,
    ( ~ v7_waybel_0(sK4(sK1,sK2))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_13
    | ~ spl13_46
    | ~ spl13_80
    | ~ spl13_86
    | ~ spl13_92
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f2614,f2508])).

fof(f2508,plain,
    ( v4_orders_2(sK4(sK1,sK2))
    | ~ spl13_13
    | ~ spl13_80
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f2502,f1378])).

fof(f1378,plain,
    ( k1_funct_1(sK2,sK8(sK2,sK4(sK1,sK2))) = sK4(sK1,sK2)
    | ~ spl13_138 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f1377,plain,
    ( spl13_138
  <=> k1_funct_1(sK2,sK8(sK2,sK4(sK1,sK2))) = sK4(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_138])])).

fof(f2502,plain,
    ( v4_orders_2(k1_funct_1(sK2,sK8(sK2,sK4(sK1,sK2))))
    | ~ spl13_13
    | ~ spl13_80 ),
    inference(resolution,[],[f2481,f861])).

fof(f861,plain,
    ( r2_hidden(sK8(sK2,sK4(sK1,sK2)),sK0)
    | ~ spl13_80 ),
    inference(avatar_component_clause,[],[f860])).

fof(f860,plain,
    ( spl13_80
  <=> r2_hidden(sK8(sK2,sK4(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_80])])).

fof(f2481,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | v4_orders_2(k1_funct_1(sK2,X3)) )
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f46,f129])).

fof(f129,plain,
    ( ~ m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_13 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl13_13
  <=> ~ m3_yellow_6(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f46,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | v4_orders_2(k1_funct_1(sK2,X3))
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <~> ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) ) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <~> ! [X3] :
                ( ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) )
                | ~ r2_hidden(X3,X0) ) )
          & v1_partfun1(X2,X0)
          & v1_funct_1(X2)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & l1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( ( v1_partfun1(X2,X0)
              & v1_funct_1(X2)
              & v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => ( m3_yellow_6(X2,X0,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                    & v7_waybel_0(k1_funct_1(X2,X3))
                    & v4_orders_2(k1_funct_1(X2,X3))
                    & ~ v2_struct_0(k1_funct_1(X2,X3)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,X0)
               => ( l1_waybel_0(k1_funct_1(X2,X3),X1)
                  & v7_waybel_0(k1_funct_1(X2,X3))
                  & v4_orders_2(k1_funct_1(X2,X3))
                  & ~ v2_struct_0(k1_funct_1(X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t33_yellow_6.p',t33_yellow_6)).

fof(f2614,plain,
    ( ~ v4_orders_2(sK4(sK1,sK2))
    | ~ v7_waybel_0(sK4(sK1,sK2))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_46
    | ~ spl13_80
    | ~ spl13_86
    | ~ spl13_92
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f2474,f101])).

fof(f101,plain,
    ( l1_struct_0(sK1)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl13_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f2474,plain,
    ( ~ v4_orders_2(sK4(sK1,sK2))
    | ~ v7_waybel_0(sK4(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_46
    | ~ spl13_80
    | ~ spl13_86
    | ~ spl13_92
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f2473,f2470])).

fof(f2470,plain,
    ( ~ v2_struct_0(sK4(sK1,sK2))
    | ~ spl13_46
    | ~ spl13_80
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f1394,f861])).

fof(f1394,plain,
    ( ~ v2_struct_0(sK4(sK1,sK2))
    | ~ r2_hidden(sK8(sK2,sK4(sK1,sK2)),sK0)
    | ~ spl13_46
    | ~ spl13_138 ),
    inference(superposition,[],[f505,f1378])).

fof(f505,plain,
    ( ! [X3] :
        ( ~ v2_struct_0(k1_funct_1(sK2,X3))
        | ~ r2_hidden(X3,sK0) )
    | ~ spl13_46 ),
    inference(avatar_component_clause,[],[f504])).

fof(f504,plain,
    ( spl13_46
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | ~ v2_struct_0(k1_funct_1(sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f2473,plain,
    ( v2_struct_0(sK4(sK1,sK2))
    | ~ v4_orders_2(sK4(sK1,sK2))
    | ~ v7_waybel_0(sK4(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_86
    | ~ spl13_92 ),
    inference(resolution,[],[f2469,f890])).

fof(f890,plain,
    ( l1_waybel_0(sK4(sK1,sK2),sK1)
    | ~ spl13_92 ),
    inference(avatar_component_clause,[],[f889])).

fof(f889,plain,
    ( spl13_92
  <=> l1_waybel_0(sK4(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f2469,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK4(X0,sK2),X0)
        | v2_struct_0(sK4(X0,sK2))
        | ~ v4_orders_2(sK4(X0,sK2))
        | ~ v7_waybel_0(sK4(X0,sK2))
        | ~ l1_struct_0(X0) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_86 ),
    inference(subsumption_resolution,[],[f122,f876])).

fof(f876,plain,
    ( ! [X0,X1] :
        ( ~ m3_yellow_6(sK2,X0,X1)
        | ~ l1_struct_0(X1) )
    | ~ spl13_86 ),
    inference(avatar_component_clause,[],[f875])).

fof(f875,plain,
    ( spl13_86
  <=> ! [X1,X0] :
        ( ~ l1_struct_0(X1)
        | ~ m3_yellow_6(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_86])])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK4(X0,sK2),X0)
        | v2_struct_0(sK4(X0,sK2))
        | ~ v4_orders_2(sK4(X0,sK2))
        | ~ v7_waybel_0(sK4(X0,sK2))
        | ~ l1_struct_0(X0)
        | m3_yellow_6(sK2,sK0,X0) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f121,f97])).

fof(f97,plain,
    ( v1_funct_1(sK2)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl13_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK2)
        | ~ l1_struct_0(X0)
        | v2_struct_0(sK4(X0,sK2))
        | ~ v4_orders_2(sK4(X0,sK2))
        | ~ v7_waybel_0(sK4(X0,sK2))
        | ~ l1_waybel_0(sK4(X0,sK2),X0)
        | m3_yellow_6(sK2,sK0,X0) )
    | ~ spl13_0
    | ~ spl13_6
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f120,f110])).

fof(f110,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl13_6
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK2,sK0)
        | ~ v1_funct_1(sK2)
        | ~ l1_struct_0(X0)
        | v2_struct_0(sK4(X0,sK2))
        | ~ v4_orders_2(sK4(X0,sK2))
        | ~ v7_waybel_0(sK4(X0,sK2))
        | ~ l1_waybel_0(sK4(X0,sK2),X0)
        | m3_yellow_6(sK2,sK0,X0) )
    | ~ spl13_0
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f117,f93])).

fof(f93,plain,
    ( v1_relat_1(sK2)
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl13_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v4_relat_1(sK2,sK0)
        | ~ v1_funct_1(sK2)
        | ~ l1_struct_0(X0)
        | v2_struct_0(sK4(X0,sK2))
        | ~ v4_orders_2(sK4(X0,sK2))
        | ~ v7_waybel_0(sK4(X0,sK2))
        | ~ l1_waybel_0(sK4(X0,sK2),X0)
        | m3_yellow_6(sK2,sK0,X0) )
    | ~ spl13_8 ),
    inference(resolution,[],[f114,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(sK4(X1,X2))
      | ~ v4_orders_2(sK4(X1,X2))
      | ~ v7_waybel_0(sK4(X1,X2))
      | ~ l1_waybel_0(sK4(X1,X2),X1)
      | m3_yellow_6(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) )
                | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) )
                | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
          | ~ v1_partfun1(X2,X0)
          | ~ v1_funct_1(X2)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ l1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( m3_yellow_6(X2,X0,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k2_relat_1(X2))
               => ( l1_waybel_0(X3,X1)
                  & v7_waybel_0(X3)
                  & v4_orders_2(X3)
                  & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t33_yellow_6.p',d15_yellow_6)).

fof(f114,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl13_8
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f2535,plain,
    ( v7_waybel_0(sK4(sK1,sK2))
    | ~ spl13_13
    | ~ spl13_80
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f2529,f1378])).

fof(f2529,plain,
    ( v7_waybel_0(k1_funct_1(sK2,sK8(sK2,sK4(sK1,sK2))))
    | ~ spl13_13
    | ~ spl13_80 ),
    inference(resolution,[],[f2482,f861])).

fof(f2482,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | v7_waybel_0(k1_funct_1(sK2,X3)) )
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f47,f129])).

fof(f47,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | v7_waybel_0(k1_funct_1(sK2,X3))
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2613,plain,
    ( ~ spl13_4
    | ~ spl13_12
    | ~ spl13_86 ),
    inference(avatar_contradiction_clause,[],[f2612])).

fof(f2612,plain,
    ( $false
    | ~ spl13_4
    | ~ spl13_12
    | ~ spl13_86 ),
    inference(subsumption_resolution,[],[f2611,f101])).

fof(f2611,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl13_12
    | ~ spl13_86 ),
    inference(resolution,[],[f876,f502])).

fof(f502,plain,
    ( m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_12 ),
    inference(avatar_component_clause,[],[f501])).

fof(f501,plain,
    ( spl13_12
  <=> m3_yellow_6(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f2585,plain,
    ( spl13_92
    | spl13_13
    | ~ spl13_80
    | ~ spl13_138 ),
    inference(avatar_split_clause,[],[f2564,f1377,f860,f128,f889])).

fof(f2564,plain,
    ( l1_waybel_0(sK4(sK1,sK2),sK1)
    | ~ spl13_13
    | ~ spl13_80
    | ~ spl13_138 ),
    inference(forward_demodulation,[],[f2555,f1378])).

fof(f2555,plain,
    ( l1_waybel_0(k1_funct_1(sK2,sK8(sK2,sK4(sK1,sK2))),sK1)
    | ~ spl13_13
    | ~ spl13_80 ),
    inference(resolution,[],[f2483,f861])).

fof(f2483,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK0)
        | l1_waybel_0(k1_funct_1(sK2,X3),sK1) )
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f48,f129])).

fof(f48,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | l1_waybel_0(k1_funct_1(sK2,X3),sK1)
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2468,plain,
    ( ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | spl13_13
    | ~ spl13_46
    | ~ spl13_80
    | ~ spl13_88
    | ~ spl13_90
    | ~ spl13_92
    | ~ spl13_138 ),
    inference(avatar_contradiction_clause,[],[f2467])).

fof(f2467,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_13
    | ~ spl13_46
    | ~ spl13_80
    | ~ spl13_88
    | ~ spl13_90
    | ~ spl13_92
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f2466,f861])).

fof(f2466,plain,
    ( ~ r2_hidden(sK8(sK2,sK4(sK1,sK2)),sK0)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_13
    | ~ spl13_46
    | ~ spl13_88
    | ~ spl13_90
    | ~ spl13_92
    | ~ spl13_138 ),
    inference(subsumption_resolution,[],[f1394,f2465])).

fof(f2465,plain,
    ( v2_struct_0(sK4(sK1,sK2))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_13
    | ~ spl13_88
    | ~ spl13_90
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f2464,f129])).

fof(f2464,plain,
    ( v2_struct_0(sK4(sK1,sK2))
    | m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_88
    | ~ spl13_90
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f2463,f101])).

fof(f2463,plain,
    ( v2_struct_0(sK4(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_88
    | ~ spl13_90
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f2462,f884])).

fof(f884,plain,
    ( v7_waybel_0(sK4(sK1,sK2))
    | ~ spl13_90 ),
    inference(avatar_component_clause,[],[f883])).

fof(f883,plain,
    ( spl13_90
  <=> v7_waybel_0(sK4(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).

fof(f2462,plain,
    ( v2_struct_0(sK4(sK1,sK2))
    | ~ v7_waybel_0(sK4(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_88
    | ~ spl13_92 ),
    inference(subsumption_resolution,[],[f896,f880])).

fof(f880,plain,
    ( v4_orders_2(sK4(sK1,sK2))
    | ~ spl13_88 ),
    inference(avatar_component_clause,[],[f879])).

fof(f879,plain,
    ( spl13_88
  <=> v4_orders_2(sK4(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_88])])).

fof(f896,plain,
    ( v2_struct_0(sK4(sK1,sK2))
    | ~ v4_orders_2(sK4(sK1,sK2))
    | ~ v7_waybel_0(sK4(sK1,sK2))
    | ~ l1_struct_0(sK1)
    | m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_92 ),
    inference(resolution,[],[f890,f122])).

fof(f2438,plain,
    ( ~ spl13_51
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_12
    | ~ spl13_52
    | spl13_55
    | ~ spl13_68 ),
    inference(avatar_split_clause,[],[f2436,f763,f1381,f1488,f501,f100,f96,f92,f517])).

fof(f517,plain,
    ( spl13_51
  <=> ~ v7_waybel_0(k1_funct_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_51])])).

fof(f1488,plain,
    ( spl13_52
  <=> v4_orders_2(k1_funct_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_52])])).

fof(f1381,plain,
    ( spl13_55
  <=> ~ v2_struct_0(k1_funct_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_55])])).

fof(f763,plain,
    ( spl13_68
  <=> r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_68])])).

fof(f2436,plain,
    ( ~ v7_waybel_0(k1_funct_1(sK2,sK3))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_12
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f2435,f502])).

fof(f2435,plain,
    ( ~ v7_waybel_0(k1_funct_1(sK2,sK3))
    | ~ m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_12
    | ~ spl13_52
    | ~ spl13_55
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f2434,f2432])).

fof(f2432,plain,
    ( l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_12
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f2428,f101])).

fof(f2428,plain,
    ( l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
    | ~ l1_struct_0(sK1)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_12
    | ~ spl13_68 ),
    inference(resolution,[],[f830,f502])).

fof(f830,plain,
    ( ! [X6,X7] :
        ( ~ m3_yellow_6(sK2,X6,X7)
        | l1_waybel_0(k1_funct_1(sK2,sK3),X7)
        | ~ l1_struct_0(X7) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f829,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m3_yellow_6(X2,X0,X1)
      | ~ l1_struct_0(X1)
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
          | ~ m3_yellow_6(X2,X0,X1) )
      | ~ l1_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( m3_yellow_6(X2,X0,X1)
         => ( v1_partfun1(X2,X0)
            & v1_funct_1(X2)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t33_yellow_6.p',dt_m3_yellow_6)).

fof(f829,plain,
    ( ! [X6,X7] :
        ( ~ v4_relat_1(sK2,X6)
        | ~ l1_struct_0(X7)
        | l1_waybel_0(k1_funct_1(sK2,sK3),X7)
        | ~ m3_yellow_6(sK2,X6,X7) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f828,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m3_yellow_6(X2,X0,X1)
      | ~ l1_struct_0(X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f828,plain,
    ( ! [X6,X7] :
        ( ~ v4_relat_1(sK2,X6)
        | ~ v1_partfun1(sK2,X6)
        | ~ l1_struct_0(X7)
        | l1_waybel_0(k1_funct_1(sK2,sK3),X7)
        | ~ m3_yellow_6(sK2,X6,X7) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f827,f97])).

fof(f827,plain,
    ( ! [X6,X7] :
        ( ~ v4_relat_1(sK2,X6)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X6)
        | ~ l1_struct_0(X7)
        | l1_waybel_0(k1_funct_1(sK2,sK3),X7)
        | ~ m3_yellow_6(sK2,X6,X7) )
    | ~ spl13_0
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f811,f93])).

fof(f811,plain,
    ( ! [X6,X7] :
        ( ~ v1_relat_1(sK2)
        | ~ v4_relat_1(sK2,X6)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X6)
        | ~ l1_struct_0(X7)
        | l1_waybel_0(k1_funct_1(sK2,sK3),X7)
        | ~ m3_yellow_6(sK2,X6,X7) )
    | ~ spl13_68 ),
    inference(resolution,[],[f764,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ l1_struct_0(X1)
      | l1_waybel_0(X3,X1)
      | ~ m3_yellow_6(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f764,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2))
    | ~ spl13_68 ),
    inference(avatar_component_clause,[],[f763])).

fof(f2434,plain,
    ( ~ v7_waybel_0(k1_funct_1(sK2,sK3))
    | ~ l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
    | ~ m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_52
    | ~ spl13_55 ),
    inference(subsumption_resolution,[],[f2433,f1489])).

fof(f1489,plain,
    ( v4_orders_2(k1_funct_1(sK2,sK3))
    | ~ spl13_52 ),
    inference(avatar_component_clause,[],[f1488])).

fof(f2433,plain,
    ( ~ v4_orders_2(k1_funct_1(sK2,sK3))
    | ~ v7_waybel_0(k1_funct_1(sK2,sK3))
    | ~ l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
    | ~ m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_55 ),
    inference(subsumption_resolution,[],[f49,f1382])).

fof(f1382,plain,
    ( ~ v2_struct_0(k1_funct_1(sK2,sK3))
    | ~ spl13_55 ),
    inference(avatar_component_clause,[],[f1381])).

fof(f49,plain,
    ( v2_struct_0(k1_funct_1(sK2,sK3))
    | ~ v4_orders_2(k1_funct_1(sK2,sK3))
    | ~ v7_waybel_0(k1_funct_1(sK2,sK3))
    | ~ l1_waybel_0(k1_funct_1(sK2,sK3),sK1)
    | ~ m3_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f1494,plain,
    ( spl13_50
    | spl13_86
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(avatar_split_clause,[],[f826,f763,f96,f92,f875,f1492])).

fof(f1492,plain,
    ( spl13_50
  <=> v7_waybel_0(k1_funct_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f826,plain,
    ( ! [X4,X5] :
        ( ~ l1_struct_0(X5)
        | v7_waybel_0(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X4,X5) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f825,f75])).

fof(f825,plain,
    ( ! [X4,X5] :
        ( ~ v4_relat_1(sK2,X4)
        | ~ l1_struct_0(X5)
        | v7_waybel_0(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X4,X5) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f824,f77])).

fof(f824,plain,
    ( ! [X4,X5] :
        ( ~ v4_relat_1(sK2,X4)
        | ~ v1_partfun1(sK2,X4)
        | ~ l1_struct_0(X5)
        | v7_waybel_0(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X4,X5) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f823,f97])).

fof(f823,plain,
    ( ! [X4,X5] :
        ( ~ v4_relat_1(sK2,X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X4)
        | ~ l1_struct_0(X5)
        | v7_waybel_0(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X4,X5) )
    | ~ spl13_0
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f810,f93])).

fof(f810,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(sK2)
        | ~ v4_relat_1(sK2,X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X4)
        | ~ l1_struct_0(X5)
        | v7_waybel_0(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X4,X5) )
    | ~ spl13_68 ),
    inference(resolution,[],[f764,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ l1_struct_0(X1)
      | v7_waybel_0(X3)
      | ~ m3_yellow_6(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1490,plain,
    ( spl13_52
    | spl13_86
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(avatar_split_clause,[],[f822,f763,f96,f92,f875,f1488])).

fof(f822,plain,
    ( ! [X2,X3] :
        ( ~ l1_struct_0(X3)
        | v4_orders_2(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X2,X3) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f821,f75])).

fof(f821,plain,
    ( ! [X2,X3] :
        ( ~ v4_relat_1(sK2,X2)
        | ~ l1_struct_0(X3)
        | v4_orders_2(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X2,X3) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f820,f77])).

fof(f820,plain,
    ( ! [X2,X3] :
        ( ~ v4_relat_1(sK2,X2)
        | ~ v1_partfun1(sK2,X2)
        | ~ l1_struct_0(X3)
        | v4_orders_2(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X2,X3) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f819,f97])).

fof(f819,plain,
    ( ! [X2,X3] :
        ( ~ v4_relat_1(sK2,X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X2)
        | ~ l1_struct_0(X3)
        | v4_orders_2(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X2,X3) )
    | ~ spl13_0
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f809,f93])).

fof(f809,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK2)
        | ~ v4_relat_1(sK2,X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X2)
        | ~ l1_struct_0(X3)
        | v4_orders_2(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X2,X3) )
    | ~ spl13_68 ),
    inference(resolution,[],[f764,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ l1_struct_0(X1)
      | v4_orders_2(X3)
      | ~ m3_yellow_6(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1383,plain,
    ( ~ spl13_55
    | spl13_86
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(avatar_split_clause,[],[f818,f763,f96,f92,f875,f1381])).

fof(f818,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X1)
        | ~ v2_struct_0(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X0,X1) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f817,f75])).

fof(f817,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(sK2,X0)
        | ~ l1_struct_0(X1)
        | ~ v2_struct_0(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X0,X1) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f816,f77])).

fof(f816,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(sK2,X0)
        | ~ v1_partfun1(sK2,X0)
        | ~ l1_struct_0(X1)
        | ~ v2_struct_0(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X0,X1) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f815,f97])).

fof(f815,plain,
    ( ! [X0,X1] :
        ( ~ v4_relat_1(sK2,X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X0)
        | ~ l1_struct_0(X1)
        | ~ v2_struct_0(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X0,X1) )
    | ~ spl13_0
    | ~ spl13_68 ),
    inference(subsumption_resolution,[],[f808,f93])).

fof(f808,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | ~ v4_relat_1(sK2,X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X0)
        | ~ l1_struct_0(X1)
        | ~ v2_struct_0(k1_funct_1(sK2,sK3))
        | ~ m3_yellow_6(sK2,X0,X1) )
    | ~ spl13_68 ),
    inference(resolution,[],[f764,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | ~ l1_struct_0(X1)
      | ~ v2_struct_0(X3)
      | ~ m3_yellow_6(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1379,plain,
    ( spl13_138
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f269,f256,f1377])).

fof(f256,plain,
    ( spl13_26
  <=> sP7(sK4(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f269,plain,
    ( k1_funct_1(sK2,sK8(sK2,sK4(sK1,sK2))) = sK4(sK1,sK2)
    | ~ spl13_26 ),
    inference(resolution,[],[f257,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ sP7(X2,X0)
      | k1_funct_1(X0,sK8(X0,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t33_yellow_6.p',d5_funct_1)).

fof(f257,plain,
    ( sP7(sK4(sK1,sK2),sK2)
    | ~ spl13_26 ),
    inference(avatar_component_clause,[],[f256])).

fof(f885,plain,
    ( spl13_90
    | spl13_86
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f606,f221,f96,f92,f875,f883])).

fof(f221,plain,
    ( spl13_22
  <=> r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f606,plain,
    ( ! [X4,X5] :
        ( ~ l1_struct_0(X5)
        | v7_waybel_0(sK4(sK1,sK2))
        | ~ m3_yellow_6(sK2,X4,X5) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f605,f75])).

fof(f605,plain,
    ( ! [X4,X5] :
        ( ~ v4_relat_1(sK2,X4)
        | ~ l1_struct_0(X5)
        | v7_waybel_0(sK4(sK1,sK2))
        | ~ m3_yellow_6(sK2,X4,X5) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f604,f77])).

fof(f604,plain,
    ( ! [X4,X5] :
        ( ~ v4_relat_1(sK2,X4)
        | ~ v1_partfun1(sK2,X4)
        | ~ l1_struct_0(X5)
        | v7_waybel_0(sK4(sK1,sK2))
        | ~ m3_yellow_6(sK2,X4,X5) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f603,f97])).

fof(f603,plain,
    ( ! [X4,X5] :
        ( ~ v4_relat_1(sK2,X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X4)
        | ~ l1_struct_0(X5)
        | v7_waybel_0(sK4(sK1,sK2))
        | ~ m3_yellow_6(sK2,X4,X5) )
    | ~ spl13_0
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f590,f93])).

fof(f590,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(sK2)
        | ~ v4_relat_1(sK2,X4)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X4)
        | ~ l1_struct_0(X5)
        | v7_waybel_0(sK4(sK1,sK2))
        | ~ m3_yellow_6(sK2,X4,X5) )
    | ~ spl13_22 ),
    inference(resolution,[],[f222,f59])).

fof(f222,plain,
    ( r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f221])).

fof(f881,plain,
    ( spl13_88
    | spl13_86
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f602,f221,f96,f92,f875,f879])).

fof(f602,plain,
    ( ! [X2,X3] :
        ( ~ l1_struct_0(X3)
        | v4_orders_2(sK4(sK1,sK2))
        | ~ m3_yellow_6(sK2,X2,X3) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f601,f75])).

fof(f601,plain,
    ( ! [X2,X3] :
        ( ~ v4_relat_1(sK2,X2)
        | ~ l1_struct_0(X3)
        | v4_orders_2(sK4(sK1,sK2))
        | ~ m3_yellow_6(sK2,X2,X3) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f600,f77])).

fof(f600,plain,
    ( ! [X2,X3] :
        ( ~ v4_relat_1(sK2,X2)
        | ~ v1_partfun1(sK2,X2)
        | ~ l1_struct_0(X3)
        | v4_orders_2(sK4(sK1,sK2))
        | ~ m3_yellow_6(sK2,X2,X3) )
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f599,f97])).

fof(f599,plain,
    ( ! [X2,X3] :
        ( ~ v4_relat_1(sK2,X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X2)
        | ~ l1_struct_0(X3)
        | v4_orders_2(sK4(sK1,sK2))
        | ~ m3_yellow_6(sK2,X2,X3) )
    | ~ spl13_0
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f589,f93])).

fof(f589,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK2)
        | ~ v4_relat_1(sK2,X2)
        | ~ v1_funct_1(sK2)
        | ~ v1_partfun1(sK2,X2)
        | ~ l1_struct_0(X3)
        | v4_orders_2(sK4(sK1,sK2))
        | ~ m3_yellow_6(sK2,X2,X3) )
    | ~ spl13_22 ),
    inference(resolution,[],[f222,f58])).

fof(f862,plain,
    ( spl13_80
    | ~ spl13_16
    | ~ spl13_26 ),
    inference(avatar_split_clause,[],[f271,f256,f139,f860])).

fof(f139,plain,
    ( spl13_16
  <=> k1_relat_1(sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f271,plain,
    ( r2_hidden(sK8(sK2,sK4(sK1,sK2)),sK0)
    | ~ spl13_16
    | ~ spl13_26 ),
    inference(forward_demodulation,[],[f268,f140])).

fof(f140,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f268,plain,
    ( r2_hidden(sK8(sK2,sK4(sK1,sK2)),k1_relat_1(sK2))
    | ~ spl13_26 ),
    inference(resolution,[],[f257,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ sP7(X2,X0)
      | r2_hidden(sK8(X0,X2),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f765,plain,
    ( spl13_68
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_56 ),
    inference(avatar_split_clause,[],[f707,f553,f96,f92,f763])).

fof(f553,plain,
    ( spl13_56
  <=> sP7(k1_funct_1(sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f707,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f706,f93])).

fof(f706,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2))
    | ~ spl13_2
    | ~ spl13_56 ),
    inference(subsumption_resolution,[],[f704,f97])).

fof(f704,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(k1_funct_1(sK2,sK3),k2_relat_1(sK2))
    | ~ spl13_56 ),
    inference(resolution,[],[f554,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( ~ sP7(X2,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP7(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f554,plain,
    ( sP7(k1_funct_1(sK2,sK3),sK2)
    | ~ spl13_56 ),
    inference(avatar_component_clause,[],[f553])).

fof(f555,plain,
    ( spl13_56
    | ~ spl13_14
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f492,f139,f131,f553])).

fof(f131,plain,
    ( spl13_14
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f492,plain,
    ( sP7(k1_funct_1(sK2,sK3),sK2)
    | ~ spl13_14
    | ~ spl13_16 ),
    inference(resolution,[],[f132,f150])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | sP7(k1_funct_1(sK2,X0),sK2) )
    | ~ spl13_16 ),
    inference(superposition,[],[f89,f140])).

fof(f89,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | sP7(k1_funct_1(X0,X3),X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | sP7(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f132,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f506,plain,
    ( spl13_12
    | spl13_46 ),
    inference(avatar_split_clause,[],[f45,f504,f501])).

fof(f45,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | ~ v2_struct_0(k1_funct_1(sK2,X3))
      | m3_yellow_6(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f258,plain,
    ( spl13_26
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f233,f221,f96,f92,f256])).

fof(f233,plain,
    ( sP7(sK4(sK1,sK2),sK2)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f232,f93])).

fof(f232,plain,
    ( sP7(sK4(sK1,sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl13_2
    | ~ spl13_22 ),
    inference(subsumption_resolution,[],[f224,f97])).

fof(f224,plain,
    ( ~ v1_funct_1(sK2)
    | sP7(sK4(sK1,sK2),sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl13_22 ),
    inference(resolution,[],[f222,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | sP7(X2,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP7(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f223,plain,
    ( spl13_22
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | spl13_13 ),
    inference(avatar_split_clause,[],[f209,f128,f113,f109,f100,f96,f92,f221])).

fof(f209,plain,
    ( r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8
    | ~ spl13_13 ),
    inference(subsumption_resolution,[],[f208,f129])).

fof(f208,plain,
    ( r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))
    | m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_0
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f207,f93])).

fof(f207,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))
    | m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_2
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f206,f97])).

fof(f206,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))
    | m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_4
    | ~ spl13_6
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f205,f110])).

fof(f205,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(sK4(sK1,sK2),k2_relat_1(sK2))
    | m3_yellow_6(sK2,sK0,sK1)
    | ~ spl13_4
    | ~ spl13_8 ),
    inference(resolution,[],[f107,f114])).

fof(f107,plain,
    ( ! [X2,X1] :
        ( ~ v1_partfun1(X1,X2)
        | ~ v4_relat_1(X1,X2)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | r2_hidden(sK4(sK1,X1),k2_relat_1(X1))
        | m3_yellow_6(X1,X2,sK1) )
    | ~ spl13_4 ),
    inference(resolution,[],[f101,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | r2_hidden(sK4(X1,X2),k2_relat_1(X2))
      | m3_yellow_6(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f141,plain,
    ( spl13_16
    | ~ spl13_0
    | ~ spl13_6
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f119,f113,f109,f92,f139])).

fof(f119,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl13_0
    | ~ spl13_6
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f118,f93])).

fof(f118,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ v1_relat_1(sK2)
    | ~ spl13_6
    | ~ spl13_8 ),
    inference(subsumption_resolution,[],[f116,f110])).

fof(f116,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | k1_relat_1(sK2) = sK0
    | ~ v1_relat_1(sK2)
    | ~ spl13_8 ),
    inference(resolution,[],[f114,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_6__t33_yellow_6.p',d4_partfun1)).

fof(f133,plain,
    ( ~ spl13_13
    | spl13_14 ),
    inference(avatar_split_clause,[],[f50,f131,f128])).

fof(f50,plain,
    ( r2_hidden(sK3,sK0)
    | ~ m3_yellow_6(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f115,plain,(
    spl13_8 ),
    inference(avatar_split_clause,[],[f54,f113])).

fof(f54,plain,(
    v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f111,plain,(
    spl13_6 ),
    inference(avatar_split_clause,[],[f52,f109])).

fof(f52,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f102,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f55,f100])).

fof(f55,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f98,plain,(
    spl13_2 ),
    inference(avatar_split_clause,[],[f53,f96])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f94,plain,(
    spl13_0 ),
    inference(avatar_split_clause,[],[f51,f92])).

fof(f51,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
