%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : filter_1__t56_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:10 EDT 2019

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  387 ( 899 expanded)
%              Number of leaves         :   68 ( 338 expanded)
%              Depth                    :   17
%              Number of atoms          : 2172 (4208 expanded)
%              Number of equality atoms :   34 (  59 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2891,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f178,f185,f192,f199,f234,f241,f248,f295,f300,f305,f310,f335,f338,f374,f377,f382,f429,f434,f468,f473,f581,f585,f600,f667,f680,f715,f726,f1145,f1156,f1166,f1246,f1261,f2204,f2287,f2304,f2354,f2802,f2853,f2882])).

fof(f2882,plain,
    ( spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_30
    | spl10_165 ),
    inference(avatar_contradiction_clause,[],[f2881])).

fof(f2881,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_30
    | ~ spl10_165 ),
    inference(subsumption_resolution,[],[f2880,f247])).

fof(f247,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl10_12
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f2880,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_30
    | ~ spl10_165 ),
    inference(subsumption_resolution,[],[f2875,f233])).

fof(f233,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl10_8
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f2875,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_30
    | ~ spl10_165 ),
    inference(resolution,[],[f2852,f346])).

fof(f346,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k4_lattices(sK0,X1,X0),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_30 ),
    inference(duplicate_literal_removal,[],[f343])).

fof(f343,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,k4_lattices(sK0,X1,X0),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_30 ),
    inference(superposition,[],[f324,f328])).

fof(f328,plain,
    ( ! [X0,X1] :
        ( k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl10_30
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f324,plain,
    ( ! [X12,X11] :
        ( r1_lattices(sK0,k4_lattices(sK0,X11,X12),X11)
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_18
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f323,f260])).

fof(f260,plain,
    ( v8_lattices(sK0)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl10_18
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f323,plain,
    ( ! [X12,X11] :
        ( ~ v8_lattices(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X11,X12),X11) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f222,f266])).

fof(f266,plain,
    ( v6_lattices(sK0)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl10_20
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f222,plain,
    ( ! [X12,X11] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X11,X12),X11) )
    | ~ spl10_1
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f209,f177])).

fof(f177,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f209,plain,
    ( ! [X12,X11] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X12,u1_struct_0(sK0))
        | r1_lattices(sK0,k4_lattices(sK0,X11,X12),X11) )
    | ~ spl10_6 ),
    inference(resolution,[],[f198,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
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
    inference(flattening,[],[f69])).

fof(f69,plain,(
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
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',t23_lattices)).

fof(f198,plain,
    ( l3_lattices(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl10_6
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f2852,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK1)
    | ~ spl10_165 ),
    inference(avatar_component_clause,[],[f2851])).

fof(f2851,plain,
    ( spl10_165
  <=> ~ r1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_165])])).

fof(f2853,plain,
    ( ~ spl10_165
    | spl10_1
    | ~ spl10_12
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_44
    | ~ spl10_50
    | ~ spl10_52
    | spl10_163 ),
    inference(avatar_split_clause,[],[f2819,f2800,f576,f570,f460,f330,f265,f246,f176,f2851])).

fof(f330,plain,
    ( spl10_32
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f460,plain,
    ( spl10_44
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2))
        | ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f570,plain,
    ( spl10_50
  <=> m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f576,plain,
    ( spl10_52
  <=> m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f2800,plain,
    ( spl10_163
  <=> ~ r1_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_163])])).

fof(f2819,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK1)
    | ~ spl10_1
    | ~ spl10_12
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_44
    | ~ spl10_50
    | ~ spl10_52
    | ~ spl10_163 ),
    inference(subsumption_resolution,[],[f2818,f247])).

fof(f2818,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_44
    | ~ spl10_50
    | ~ spl10_52
    | ~ spl10_163 ),
    inference(subsumption_resolution,[],[f2817,f571])).

fof(f571,plain,
    ( m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f570])).

fof(f2817,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_44
    | ~ spl10_52
    | ~ spl10_163 ),
    inference(subsumption_resolution,[],[f2810,f577])).

fof(f577,plain,
    ( m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ spl10_52 ),
    inference(avatar_component_clause,[],[f576])).

fof(f2810,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k4_lattices(sK0,sK3,sK1),sK1)
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_44
    | ~ spl10_163 ),
    inference(resolution,[],[f2801,f505])).

fof(f505,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),k4_lattices(sK0,X2,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_44 ),
    inference(duplicate_literal_removal,[],[f500])).

fof(f500,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattices(sK0,k4_lattices(sK0,X0,X1),k4_lattices(sK0,X2,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_44 ),
    inference(superposition,[],[f477,f350])).

fof(f350,plain,
    ( ! [X2,X3] :
        ( k4_lattices(sK0,X2,X3) = k2_lattices(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(subsumption_resolution,[],[f349,f331])).

fof(f331,plain,
    ( l1_lattices(sK0)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f330])).

fof(f349,plain,
    ( ! [X2,X3] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k4_lattices(sK0,X2,X3) = k2_lattices(sK0,X2,X3) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f201,f266])).

fof(f201,plain,
    ( ! [X2,X3] :
        ( ~ v6_lattices(sK0)
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k4_lattices(sK0,X2,X3) = k2_lattices(sK0,X2,X3) )
    | ~ spl10_1 ),
    inference(resolution,[],[f177,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',redefinition_k4_lattices)).

fof(f477,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattices(sK0,k2_lattices(sK0,X2,X1),k4_lattices(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_44 ),
    inference(duplicate_literal_removal,[],[f476])).

fof(f476,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattices(sK0,k2_lattices(sK0,X2,X1),k4_lattices(sK0,X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X2,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_44 ),
    inference(superposition,[],[f461,f350])).

fof(f461,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f460])).

fof(f2801,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)))
    | ~ spl10_163 ),
    inference(avatar_component_clause,[],[f2800])).

fof(f2802,plain,
    ( ~ spl10_163
    | ~ spl10_92
    | ~ spl10_100
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f2331,f2199,f1244,f1137,f2800])).

fof(f1137,plain,
    ( spl10_92
  <=> m1_subset_1(k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f1244,plain,
    ( spl10_100
  <=> ! [X0] :
        ( ~ r1_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f2199,plain,
    ( spl10_140
  <=> r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_140])])).

fof(f2331,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)))
    | ~ spl10_92
    | ~ spl10_100
    | ~ spl10_140 ),
    inference(subsumption_resolution,[],[f2322,f1138])).

fof(f1138,plain,
    ( m1_subset_1(k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl10_92 ),
    inference(avatar_component_clause,[],[f1137])).

fof(f2322,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)))
    | ~ spl10_100
    | ~ spl10_140 ),
    inference(resolution,[],[f2200,f1245])).

fof(f1245,plain,
    ( ! [X0] :
        ( ~ r1_lattices(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),X0) )
    | ~ spl10_100 ),
    inference(avatar_component_clause,[],[f1244])).

fof(f2200,plain,
    ( r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ spl10_140 ),
    inference(avatar_component_clause,[],[f2199])).

fof(f2354,plain,
    ( ~ spl10_8
    | ~ spl10_12
    | ~ spl10_22
    | spl10_27
    | ~ spl10_30 ),
    inference(avatar_contradiction_clause,[],[f2353])).

fof(f2353,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_22
    | ~ spl10_27
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f2016,f288])).

fof(f288,plain,
    ( ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,k4_lattices(sK0,sK1,sK3),sK2))
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f287])).

fof(f287,plain,
    ( spl10_27
  <=> ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,k4_lattices(sK0,sK1,sK3),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f2016,plain,
    ( r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,k4_lattices(sK0,sK1,sK3),sK2))
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_22
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f2015,f233])).

fof(f2015,plain,
    ( r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,k4_lattices(sK0,sK1,sK3),sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl10_12
    | ~ spl10_22
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f2012,f247])).

fof(f2012,plain,
    ( r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,k4_lattices(sK0,sK1,sK3),sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl10_22
    | ~ spl10_30 ),
    inference(superposition,[],[f273,f328])).

fof(f273,plain,
    ( r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,k4_lattices(sK0,sK3,sK1),sK2))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl10_22
  <=> r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,k4_lattices(sK0,sK3,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f2304,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_12
    | spl10_145 ),
    inference(avatar_contradiction_clause,[],[f2303])).

fof(f2303,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_145 ),
    inference(subsumption_resolution,[],[f2302,f240])).

fof(f240,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl10_10
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f2302,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_12
    | ~ spl10_145 ),
    inference(subsumption_resolution,[],[f2300,f247])).

fof(f2300,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_145 ),
    inference(resolution,[],[f2286,f322])).

fof(f322,plain,
    ( ! [X4,X3] :
        ( r3_lattices(sK0,k4_lattices(sK0,X4,k4_filter_0(sK0,X4,X3)),X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f321,f198])).

fof(f321,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r3_lattices(sK0,k4_lattices(sK0,X4,k4_filter_0(sK0,X4,X3)),X3) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f320,f191])).

fof(f191,plain,
    ( v3_filter_0(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl10_4
  <=> v3_filter_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f320,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v3_filter_0(sK0)
        | ~ l3_lattices(sK0)
        | r3_lattices(sK0,k4_lattices(sK0,X4,k4_filter_0(sK0,X4,X3)),X3) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f319,f184])).

fof(f184,plain,
    ( v10_lattices(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl10_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f319,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v10_lattices(sK0)
        | ~ v3_filter_0(sK0)
        | ~ l3_lattices(sK0)
        | r3_lattices(sK0,k4_lattices(sK0,X4,k4_filter_0(sK0,X4,X3)),X3) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f313,f177])).

fof(f313,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v10_lattices(sK0)
        | ~ v3_filter_0(sK0)
        | ~ l3_lattices(sK0)
        | r3_lattices(sK0,k4_lattices(sK0,X4,k4_filter_0(sK0,X4,X3)),X3) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(duplicate_literal_removal,[],[f312])).

fof(f312,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v10_lattices(sK0)
        | ~ v3_filter_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r3_lattices(sK0,k4_lattices(sK0,X4,k4_filter_0(sK0,X4,X3)),X3) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(resolution,[],[f224,f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r3_lattices(X0,k4_lattices(X0,X1,k4_filter_0(X0,X1,X2)),X2) ) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r3_lattices(X0,k4_lattices(X0,X1,X3),X2)
      | k4_filter_0(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_filter_0(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r3_lattices(X0,X4,X3)
                          | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l3_lattices(X0)
              | ~ v3_filter_0(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_filter_0(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r3_lattices(X0,X4,X3)
                          | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l3_lattices(X0)
              | ~ v3_filter_0(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( l3_lattices(X0)
                  & v3_filter_0(X0)
                  & v10_lattices(X0)
                  & ~ v2_struct_0(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( k4_filter_0(X0,X1,X2) = X3
                    <=> ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                             => r3_lattices(X0,X4,X3) ) )
                        & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',d8_filter_0)).

fof(f224,plain,
    ( ! [X14,X13] :
        ( m1_subset_1(k4_filter_0(sK0,X13,X14),u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ m1_subset_1(X13,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f223,f177])).

fof(f223,plain,
    ( ! [X14,X13] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | m1_subset_1(k4_filter_0(sK0,X13,X14),u1_struct_0(sK0)) )
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f210,f184])).

fof(f210,plain,
    ( ! [X14,X13] :
        ( ~ v10_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | m1_subset_1(k4_filter_0(sK0,X13,X14),u1_struct_0(sK0)) )
    | ~ spl10_6 ),
    inference(resolution,[],[f198,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',dt_k4_filter_0)).

fof(f2286,plain,
    ( ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ spl10_145 ),
    inference(avatar_component_clause,[],[f2285])).

fof(f2285,plain,
    ( spl10_145
  <=> ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_145])])).

fof(f2287,plain,
    ( ~ spl10_145
    | spl10_1
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_92
    | spl10_141 ),
    inference(avatar_split_clause,[],[f2220,f2202,f1137,f265,f259,f253,f239,f197,f176,f2285])).

fof(f253,plain,
    ( spl10_16
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f2202,plain,
    ( spl10_141
  <=> ~ r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_141])])).

fof(f2220,plain,
    ( ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_92
    | ~ spl10_141 ),
    inference(subsumption_resolution,[],[f2219,f1138])).

fof(f2219,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_141 ),
    inference(subsumption_resolution,[],[f2216,f240])).

fof(f2216,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_141 ),
    inference(resolution,[],[f2203,f414])).

fof(f414,plain,
    ( ! [X17,X18] :
        ( r1_lattices(sK0,X17,X18)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X17,X18) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f413,f254])).

fof(f254,plain,
    ( v9_lattices(sK0)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f253])).

fof(f413,plain,
    ( ! [X17,X18] :
        ( ~ v9_lattices(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | r1_lattices(sK0,X17,X18)
        | ~ r3_lattices(sK0,X17,X18) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_18
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f412,f260])).

fof(f412,plain,
    ( ! [X17,X18] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | r1_lattices(sK0,X17,X18)
        | ~ r3_lattices(sK0,X17,X18) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f226,f266])).

fof(f226,plain,
    ( ! [X17,X18] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | r1_lattices(sK0,X17,X18)
        | ~ r3_lattices(sK0,X17,X18) )
    | ~ spl10_1
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f212,f177])).

fof(f212,plain,
    ( ! [X17,X18] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | r1_lattices(sK0,X17,X18)
        | ~ r3_lattices(sK0,X17,X18) )
    | ~ spl10_6 ),
    inference(resolution,[],[f198,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
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
    inference(flattening,[],[f87])).

fof(f87,plain,(
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
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',redefinition_r3_lattices)).

fof(f2203,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ spl10_141 ),
    inference(avatar_component_clause,[],[f2202])).

fof(f2204,plain,
    ( ~ spl10_141
    | spl10_1
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_94 ),
    inference(avatar_split_clause,[],[f2146,f1143,f421,f369,f363,f360,f239,f232,f176,f2202])).

fof(f360,plain,
    ( spl10_34
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k3_lattices(sK0,X4,X5) = k3_lattices(sK0,X5,X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f363,plain,
    ( spl10_36
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f369,plain,
    ( spl10_38
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f421,plain,
    ( spl10_40
  <=> ! [X3,X4] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_lattices(sK0,X3,k1_lattices(sK0,X3,X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f1143,plain,
    ( spl10_94
  <=> ! [X0] :
        ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,k3_lattices(sK0,sK3,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f2146,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ spl10_1
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f2145,f233])).

fof(f2145,plain,
    ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_10
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_94 ),
    inference(subsumption_resolution,[],[f2139,f240])).

fof(f2139,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_94 ),
    inference(duplicate_literal_removal,[],[f2132])).

fof(f2132,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40
    | ~ spl10_94 ),
    inference(resolution,[],[f1144,f444])).

fof(f444,plain,
    ( ! [X2,X3] :
        ( r1_lattices(sK0,X2,k3_lattices(sK0,X3,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40 ),
    inference(duplicate_literal_removal,[],[f443])).

fof(f443,plain,
    ( ! [X2,X3] :
        ( r1_lattices(sK0,X2,k3_lattices(sK0,X3,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_34
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40 ),
    inference(superposition,[],[f437,f361])).

fof(f361,plain,
    ( ! [X4,X5] :
        ( k3_lattices(sK0,X4,X5) = k3_lattices(sK0,X5,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f360])).

fof(f437,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,k3_lattices(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40 ),
    inference(duplicate_literal_removal,[],[f436])).

fof(f436,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,k3_lattices(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_40 ),
    inference(superposition,[],[f422,f390])).

fof(f390,plain,
    ( ! [X6,X7] :
        ( k3_lattices(sK0,X6,X7) = k1_lattices(sK0,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_36
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f389,f364])).

fof(f364,plain,
    ( l2_lattices(sK0)
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f363])).

fof(f389,plain,
    ( ! [X6,X7] :
        ( ~ l2_lattices(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k3_lattices(sK0,X6,X7) = k1_lattices(sK0,X6,X7) )
    | ~ spl10_1
    | ~ spl10_38 ),
    inference(subsumption_resolution,[],[f203,f370])).

fof(f370,plain,
    ( v4_lattices(sK0)
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f369])).

fof(f203,plain,
    ( ! [X6,X7] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | k3_lattices(sK0,X6,X7) = k1_lattices(sK0,X6,X7) )
    | ~ spl10_1 ),
    inference(resolution,[],[f177,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',redefinition_k3_lattices)).

fof(f422,plain,
    ( ! [X4,X3] :
        ( r1_lattices(sK0,X3,k1_lattices(sK0,X3,X4))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f421])).

fof(f1144,plain,
    ( ! [X0] :
        ( ~ r1_lattices(sK0,X0,k3_lattices(sK0,sK3,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),X0) )
    | ~ spl10_94 ),
    inference(avatar_component_clause,[],[f1143])).

fof(f1261,plain,
    ( spl10_1
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_50
    | ~ spl10_52
    | spl10_99 ),
    inference(avatar_contradiction_clause,[],[f1260])).

fof(f1260,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_50
    | ~ spl10_52
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1259,f177])).

fof(f1259,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_50
    | ~ spl10_52
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1258,f571])).

fof(f1258,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_52
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1257,f577])).

fof(f1257,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1256,f331])).

fof(f1256,plain,
    ( ~ l1_lattices(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_99 ),
    inference(subsumption_resolution,[],[f1248,f266])).

fof(f1248,plain,
    ( ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_99 ),
    inference(resolution,[],[f1242,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',dt_k4_lattices)).

fof(f1242,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl10_99 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f1241,plain,
    ( spl10_99
  <=> ~ m1_subset_1(k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f1246,plain,
    ( ~ spl10_99
    | spl10_100
    | spl10_1
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_36
    | ~ spl10_42
    | spl10_49 ),
    inference(avatar_split_clause,[],[f612,f567,f424,f363,f265,f259,f253,f239,f197,f176,f1244,f1241])).

fof(f424,plain,
    ( spl10_42
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f567,plain,
    ( spl10_49
  <=> ~ r3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f612,plain,
    ( ! [X0] :
        ( ~ r1_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),X0)
        | ~ r1_lattices(sK0,X0,sK2)
        | ~ m1_subset_1(k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_36
    | ~ spl10_42
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f607,f240])).

fof(f607,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),X0)
        | ~ r1_lattices(sK0,X0,sK2)
        | ~ m1_subset_1(k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_36
    | ~ spl10_42
    | ~ spl10_49 ),
    inference(resolution,[],[f568,f449])).

fof(f449,plain,
    ( ! [X2,X0,X1] :
        ( r3_lattices(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X2,X0)
        | ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_36
    | ~ spl10_42 ),
    inference(duplicate_literal_removal,[],[f448])).

fof(f448,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X2,X0)
        | ~ r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r3_lattices(sK0,X2,X1) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_36
    | ~ spl10_42 ),
    inference(resolution,[],[f440,f401])).

fof(f401,plain,
    ( ! [X15,X16] :
        ( ~ r1_lattices(sK0,X15,X16)
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | r3_lattices(sK0,X15,X16) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f400,f254])).

fof(f400,plain,
    ( ! [X15,X16] :
        ( ~ v9_lattices(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X15,X16)
        | r3_lattices(sK0,X15,X16) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_18
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f399,f260])).

fof(f399,plain,
    ( ! [X15,X16] :
        ( ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X15,X16)
        | r3_lattices(sK0,X15,X16) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f225,f266])).

fof(f225,plain,
    ( ! [X15,X16] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X15,X16)
        | r3_lattices(sK0,X15,X16) )
    | ~ spl10_1
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f211,f177])).

fof(f211,plain,
    ( ! [X15,X16] :
        ( ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X15,u1_struct_0(sK0))
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X15,X16)
        | r3_lattices(sK0,X15,X16) )
    | ~ spl10_6 ),
    inference(resolution,[],[f198,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f440,plain,
    ( ! [X10,X8,X9] :
        ( r1_lattices(sK0,X8,X10)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X8,X9)
        | ~ r1_lattices(sK0,X9,X10)
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_36
    | ~ spl10_42 ),
    inference(subsumption_resolution,[],[f439,f364])).

fof(f439,plain,
    ( ! [X10,X8,X9] :
        ( ~ l2_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X8,X9)
        | ~ r1_lattices(sK0,X9,X10)
        | r1_lattices(sK0,X8,X10) )
    | ~ spl10_1
    | ~ spl10_42 ),
    inference(subsumption_resolution,[],[f204,f425])).

fof(f425,plain,
    ( v5_lattices(sK0)
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f424])).

fof(f204,plain,
    ( ! [X10,X8,X9] :
        ( ~ v5_lattices(sK0)
        | ~ l2_lattices(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X8,X9)
        | ~ r1_lattices(sK0,X9,X10)
        | r1_lattices(sK0,X8,X10) )
    | ~ spl10_1 ),
    inference(resolution,[],[f177,f134])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v5_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | ~ r1_lattices(X0,X2,X3)
      | r1_lattices(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r1_lattices(X0,X2,X3)
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r1_lattices(X0,X2,X3)
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_lattices(X0,X2,X3)
                      & r1_lattices(X0,X1,X2) )
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',t25_lattices)).

fof(f568,plain,
    ( ~ r3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f567])).

fof(f1166,plain,
    ( ~ spl10_8
    | ~ spl10_10
    | ~ spl10_34
    | ~ spl10_60
    | spl10_67 ),
    inference(avatar_contradiction_clause,[],[f1165])).

fof(f1165,plain,
    ( $false
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_34
    | ~ spl10_60
    | ~ spl10_67 ),
    inference(subsumption_resolution,[],[f1164,f240])).

fof(f1164,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_8
    | ~ spl10_34
    | ~ spl10_60
    | ~ spl10_67 ),
    inference(subsumption_resolution,[],[f1163,f233])).

fof(f1163,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_34
    | ~ spl10_60
    | ~ spl10_67 ),
    inference(subsumption_resolution,[],[f1158,f714])).

fof(f714,plain,
    ( ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK2,sK3))
    | ~ spl10_67 ),
    inference(avatar_component_clause,[],[f713])).

fof(f713,plain,
    ( spl10_67
  <=> ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).

fof(f1158,plain,
    ( r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_34
    | ~ spl10_60 ),
    inference(superposition,[],[f663,f361])).

fof(f663,plain,
    ( r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK3,sK2))
    | ~ spl10_60 ),
    inference(avatar_component_clause,[],[f662])).

fof(f662,plain,
    ( spl10_60
  <=> r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f1156,plain,
    ( spl10_1
    | ~ spl10_12
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_50
    | spl10_93 ),
    inference(avatar_contradiction_clause,[],[f1155])).

fof(f1155,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_12
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_50
    | ~ spl10_93 ),
    inference(subsumption_resolution,[],[f1154,f177])).

fof(f1154,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_12
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_50
    | ~ spl10_93 ),
    inference(subsumption_resolution,[],[f1153,f571])).

fof(f1153,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_12
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_93 ),
    inference(subsumption_resolution,[],[f1152,f247])).

fof(f1152,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_93 ),
    inference(subsumption_resolution,[],[f1151,f331])).

fof(f1151,plain,
    ( ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_93 ),
    inference(subsumption_resolution,[],[f1147,f266])).

fof(f1147,plain,
    ( ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_93 ),
    inference(resolution,[],[f1141,f156])).

fof(f1141,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl10_93 ),
    inference(avatar_component_clause,[],[f1140])).

fof(f1140,plain,
    ( spl10_93
  <=> ~ m1_subset_1(k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f1145,plain,
    ( ~ spl10_93
    | spl10_94
    | spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_36
    | ~ spl10_42
    | ~ spl10_58
    | spl10_61 ),
    inference(avatar_split_clause,[],[f690,f665,f656,f424,f363,f265,f259,f253,f197,f176,f1143,f1140])).

fof(f656,plain,
    ( spl10_58
  <=> m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f665,plain,
    ( spl10_61
  <=> ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f690,plain,
    ( ! [X0] :
        ( ~ r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),X0)
        | ~ r1_lattices(sK0,X0,k3_lattices(sK0,sK3,sK2))
        | ~ m1_subset_1(k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_36
    | ~ spl10_42
    | ~ spl10_58
    | ~ spl10_61 ),
    inference(subsumption_resolution,[],[f687,f657])).

fof(f657,plain,
    ( m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f656])).

fof(f687,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
        | ~ r1_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),X0)
        | ~ r1_lattices(sK0,X0,k3_lattices(sK0,sK3,sK2))
        | ~ m1_subset_1(k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_36
    | ~ spl10_42
    | ~ spl10_61 ),
    inference(resolution,[],[f666,f449])).

fof(f666,plain,
    ( ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK3,sK2))
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f665])).

fof(f726,plain,
    ( spl10_1
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_36
    | ~ spl10_38
    | spl10_65 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f724,f177])).

fof(f724,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f723,f233])).

fof(f723,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_10
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f722,f240])).

fof(f722,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f721,f364])).

fof(f721,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_38
    | ~ spl10_65 ),
    inference(subsumption_resolution,[],[f717,f370])).

fof(f717,plain,
    ( ~ v4_lattices(sK0)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_65 ),
    inference(resolution,[],[f708,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
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
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',dt_k3_lattices)).

fof(f708,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl10_65 ),
    inference(avatar_component_clause,[],[f707])).

fof(f707,plain,
    ( spl10_65
  <=> ~ m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f715,plain,
    ( ~ spl10_65
    | ~ spl10_67
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_12
    | spl10_29
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f695,f570,f293,f246,f197,f190,f183,f176,f713,f707])).

fof(f293,plain,
    ( spl10_29
  <=> ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK1,k3_lattices(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f695,plain,
    ( ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_12
    | ~ spl10_29
    | ~ spl10_50 ),
    inference(subsumption_resolution,[],[f497,f571])).

fof(f497,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_12
    | ~ spl10_29 ),
    inference(subsumption_resolution,[],[f492,f247])).

fof(f492,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK2,sK3))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_29 ),
    inference(resolution,[],[f318,f294])).

fof(f294,plain,
    ( ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK1,k3_lattices(sK0,sK2,sK3)))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f293])).

fof(f318,plain,
    ( ! [X2,X0,X1] :
        ( r3_lattices(sK0,X2,k4_filter_0(sK0,X1,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k4_lattices(sK0,X1,X2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f317,f198])).

fof(f317,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k4_lattices(sK0,X1,X2),X0)
        | r3_lattices(sK0,X2,k4_filter_0(sK0,X1,X0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f316,f191])).

fof(f316,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v3_filter_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k4_lattices(sK0,X1,X2),X0)
        | r3_lattices(sK0,X2,k4_filter_0(sK0,X1,X0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f315,f184])).

fof(f315,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v10_lattices(sK0)
        | ~ v3_filter_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k4_lattices(sK0,X1,X2),X0)
        | r3_lattices(sK0,X2,k4_filter_0(sK0,X1,X0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f314,f177])).

fof(f314,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v10_lattices(sK0)
        | ~ v3_filter_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k4_lattices(sK0,X1,X2),X0)
        | r3_lattices(sK0,X2,k4_filter_0(sK0,X1,X0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(duplicate_literal_removal,[],[f311])).

fof(f311,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ v10_lattices(sK0)
        | ~ v3_filter_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,k4_lattices(sK0,X1,X2),X0)
        | r3_lattices(sK0,X2,k4_filter_0(sK0,X1,X0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(resolution,[],[f224,f170])).

fof(f170,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
      | r3_lattices(X0,X4,k4_filter_0(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f138])).

fof(f138,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
      | r3_lattices(X0,X4,X3)
      | k4_filter_0(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f680,plain,
    ( spl10_1
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_36
    | ~ spl10_38
    | spl10_59 ),
    inference(avatar_contradiction_clause,[],[f679])).

fof(f679,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_59 ),
    inference(subsumption_resolution,[],[f678,f177])).

fof(f678,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_59 ),
    inference(subsumption_resolution,[],[f677,f240])).

fof(f677,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_8
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_59 ),
    inference(subsumption_resolution,[],[f676,f233])).

fof(f676,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_36
    | ~ spl10_38
    | ~ spl10_59 ),
    inference(subsumption_resolution,[],[f675,f364])).

fof(f675,plain,
    ( ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_38
    | ~ spl10_59 ),
    inference(subsumption_resolution,[],[f669,f370])).

fof(f669,plain,
    ( ~ v4_lattices(sK0)
    | ~ l2_lattices(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_59 ),
    inference(resolution,[],[f660,f149])).

fof(f660,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl10_59 ),
    inference(avatar_component_clause,[],[f659])).

fof(f659,plain,
    ( spl10_59
  <=> ~ m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_59])])).

fof(f667,plain,
    ( ~ spl10_59
    | ~ spl10_61
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_12
    | spl10_25
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f654,f570,f281,f246,f197,f190,f183,f176,f665,f659])).

fof(f281,plain,
    ( spl10_25
  <=> ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK1,k3_lattices(sK0,sK3,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f654,plain,
    ( ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK3,sK2))
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_12
    | ~ spl10_25
    | ~ spl10_50 ),
    inference(subsumption_resolution,[],[f496,f571])).

fof(f496,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK3,sK2))
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_12
    | ~ spl10_25 ),
    inference(subsumption_resolution,[],[f491,f247])).

fof(f491,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k4_lattices(sK0,sK1,k4_filter_0(sK0,sK1,sK2)),k3_lattices(sK0,sK3,sK2))
    | ~ m1_subset_1(k3_lattices(sK0,sK3,sK2),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_25 ),
    inference(resolution,[],[f318,f282])).

fof(f282,plain,
    ( ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK1,k3_lattices(sK0,sK3,sK2)))
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f281])).

fof(f600,plain,
    ( spl10_1
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_20
    | ~ spl10_32
    | spl10_53 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f598,f177])).

fof(f598,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f597,f247])).

fof(f597,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_8
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f596,f233])).

fof(f596,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_32
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f595,f331])).

fof(f595,plain,
    ( ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_20
    | ~ spl10_53 ),
    inference(subsumption_resolution,[],[f589,f266])).

fof(f589,plain,
    ( ~ v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl10_53 ),
    inference(resolution,[],[f580,f156])).

fof(f580,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f579])).

fof(f579,plain,
    ( spl10_53
  <=> ~ m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f585,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_12
    | spl10_51 ),
    inference(avatar_contradiction_clause,[],[f584])).

fof(f584,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f583,f247])).

fof(f583,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_51 ),
    inference(subsumption_resolution,[],[f582,f240])).

fof(f582,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_51 ),
    inference(resolution,[],[f574,f224])).

fof(f574,plain,
    ( ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl10_51 ),
    inference(avatar_component_clause,[],[f573])).

fof(f573,plain,
    ( spl10_51
  <=> ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f581,plain,
    ( ~ spl10_49
    | ~ spl10_51
    | ~ spl10_53
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10
    | spl10_23 ),
    inference(avatar_split_clause,[],[f494,f275,f239,f197,f190,f183,f176,f579,f573,f567])).

fof(f275,plain,
    ( spl10_23
  <=> ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,k4_lattices(sK0,sK3,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f494,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_10
    | ~ spl10_23 ),
    inference(subsumption_resolution,[],[f489,f240])).

fof(f489,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK3,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k4_filter_0(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ r3_lattices(sK0,k4_lattices(sK0,k4_lattices(sK0,sK3,sK1),k4_filter_0(sK0,sK1,sK2)),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_23 ),
    inference(resolution,[],[f318,f276])).

fof(f276,plain,
    ( ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,k4_lattices(sK0,sK3,sK1),sK2))
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f275])).

fof(f473,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | spl10_47 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f471,f198])).

fof(f471,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f470,f184])).

fof(f470,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_47 ),
    inference(subsumption_resolution,[],[f469,f177])).

fof(f469,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_47 ),
    inference(resolution,[],[f467,f129])).

fof(f129,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',cc1_lattices)).

fof(f467,plain,
    ( ~ v7_lattices(sK0)
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl10_47
  <=> ~ v7_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f468,plain,
    ( spl10_44
    | ~ spl10_47
    | spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f458,f259,f253,f197,f176,f466,f460])).

fof(f458,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f457,f254])).

fof(f457,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_18 ),
    inference(subsumption_resolution,[],[f214,f260])).

fof(f214,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2)) )
    | ~ spl10_1
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f205,f177])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( ~ v7_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattices(sK0,X0,X1)
        | r1_lattices(sK0,k2_lattices(sK0,X0,X2),k2_lattices(sK0,X1,X2)) )
    | ~ spl10_6 ),
    inference(resolution,[],[f198,f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | ~ v7_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattices(X0,X1,X2)
      | r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3))
                  | ~ r1_lattices(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattices(X0,X1,X2)
                   => r1_lattices(X0,k2_lattices(X0,X1,X3),k2_lattices(X0,X2,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',t27_lattices)).

fof(f434,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | spl10_43 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f432,f198])).

fof(f432,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f431,f184])).

fof(f431,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_43 ),
    inference(subsumption_resolution,[],[f430,f177])).

fof(f430,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_43 ),
    inference(resolution,[],[f428,f127])).

fof(f127,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f428,plain,
    ( ~ v5_lattices(sK0)
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f427])).

fof(f427,plain,
    ( spl10_43
  <=> ~ v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f429,plain,
    ( spl10_40
    | ~ spl10_43
    | spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f419,f265,f259,f253,f197,f176,f427,f421])).

fof(f419,plain,
    ( ! [X4,X3] :
        ( ~ v5_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattices(sK0,X3,k1_lattices(sK0,X3,X4)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f418,f254])).

fof(f418,plain,
    ( ! [X4,X3] :
        ( ~ v5_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattices(sK0,X3,k1_lattices(sK0,X3,X4)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_18
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f417,f260])).

fof(f417,plain,
    ( ! [X4,X3] :
        ( ~ v5_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattices(sK0,X3,k1_lattices(sK0,X3,X4)) )
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f215,f266])).

fof(f215,plain,
    ( ! [X4,X3] :
        ( ~ v5_lattices(sK0)
        | ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattices(sK0,X3,k1_lattices(sK0,X3,X4)) )
    | ~ spl10_1
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f206,f177])).

fof(f206,plain,
    ( ! [X4,X3] :
        ( ~ v5_lattices(sK0)
        | ~ v6_lattices(sK0)
        | ~ v8_lattices(sK0)
        | ~ v9_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | r1_lattices(sK0,X3,k1_lattices(sK0,X3,X4)) )
    | ~ spl10_6 ),
    inference(resolution,[],[f198,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v5_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',t22_lattices)).

fof(f382,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | spl10_39 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f380,f198])).

fof(f380,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f379,f184])).

fof(f379,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_39 ),
    inference(subsumption_resolution,[],[f378,f177])).

fof(f378,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_39 ),
    inference(resolution,[],[f373,f126])).

fof(f126,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f373,plain,
    ( ~ v4_lattices(sK0)
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl10_39
  <=> ~ v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f377,plain,
    ( ~ spl10_6
    | spl10_37 ),
    inference(avatar_contradiction_clause,[],[f376])).

fof(f376,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_37 ),
    inference(subsumption_resolution,[],[f375,f198])).

fof(f375,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl10_37 ),
    inference(resolution,[],[f367,f125])).

fof(f125,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',dt_l3_lattices)).

fof(f367,plain,
    ( ~ l2_lattices(sK0)
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f366])).

fof(f366,plain,
    ( spl10_37
  <=> ~ l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f374,plain,
    ( spl10_34
    | ~ spl10_37
    | ~ spl10_39
    | spl10_1 ),
    inference(avatar_split_clause,[],[f202,f176,f372,f366,f360])).

fof(f202,plain,
    ( ! [X4,X5] :
        ( ~ v4_lattices(sK0)
        | ~ l2_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | k3_lattices(sK0,X4,X5) = k3_lattices(sK0,X5,X4) )
    | ~ spl10_1 ),
    inference(resolution,[],[f177,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ l2_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',commutativity_k3_lattices)).

fof(f338,plain,
    ( ~ spl10_6
    | spl10_33 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_33 ),
    inference(subsumption_resolution,[],[f336,f198])).

fof(f336,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl10_33 ),
    inference(resolution,[],[f334,f124])).

fof(f124,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f334,plain,
    ( ~ l1_lattices(sK0)
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl10_33
  <=> ~ l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f335,plain,
    ( spl10_30
    | ~ spl10_33
    | spl10_1
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f325,f265,f176,f333,f327])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f200,f266])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( ~ v6_lattices(sK0)
        | ~ l1_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k4_lattices(sK0,X0,X1) = k4_lattices(sK0,X1,X0) )
    | ~ spl10_1 ),
    inference(resolution,[],[f177,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',commutativity_k4_lattices)).

fof(f310,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | spl10_21 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f308,f198])).

fof(f308,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f307,f184])).

fof(f307,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_21 ),
    inference(subsumption_resolution,[],[f306,f177])).

fof(f306,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_21 ),
    inference(resolution,[],[f269,f128])).

fof(f128,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f269,plain,
    ( ~ v6_lattices(sK0)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl10_21
  <=> ~ v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f305,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | spl10_19 ),
    inference(avatar_contradiction_clause,[],[f304])).

fof(f304,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f303,f198])).

fof(f303,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f302,f184])).

fof(f302,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f301,f177])).

fof(f301,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_19 ),
    inference(resolution,[],[f263,f130])).

fof(f130,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f263,plain,
    ( ~ v8_lattices(sK0)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl10_19
  <=> ~ v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f300,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | spl10_17 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f298,f198])).

fof(f298,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f297,f184])).

fof(f297,plain,
    ( ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_1
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f296,f177])).

fof(f296,plain,
    ( v2_struct_0(sK0)
    | ~ v10_lattices(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl10_17 ),
    inference(resolution,[],[f257,f131])).

fof(f131,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f257,plain,
    ( ~ v9_lattices(sK0)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl10_17
  <=> ~ v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f295,plain,
    ( ~ spl10_23
    | ~ spl10_25
    | ~ spl10_27
    | ~ spl10_29 ),
    inference(avatar_split_clause,[],[f106,f293,f287,f281,f275])).

fof(f106,plain,
    ( ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK1,k3_lattices(sK0,sK2,sK3)))
    | ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,k4_lattices(sK0,sK1,sK3),sK2))
    | ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,sK1,k3_lattices(sK0,sK3,sK2)))
    | ~ r3_lattices(sK0,k4_filter_0(sK0,sK1,sK2),k4_filter_0(sK0,k4_lattices(sK0,sK3,sK1),sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,k4_lattices(X0,X3,X1),X2))
                    | ~ r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X1,k3_lattices(X0,X3,X2)))
                    | ~ r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,k4_lattices(X0,X1,X3),X2))
                    | ~ r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X1,k3_lattices(X0,X2,X3))) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v3_filter_0(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,k4_lattices(X0,X3,X1),X2))
                    | ~ r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X1,k3_lattices(X0,X3,X2)))
                    | ~ r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,k4_lattices(X0,X1,X3),X2))
                    | ~ r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X1,k3_lattices(X0,X2,X3))) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v3_filter_0(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v3_filter_0(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,k4_lattices(X0,X3,X1),X2))
                      & r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X1,k3_lattices(X0,X3,X2)))
                      & r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,k4_lattices(X0,X1,X3),X2))
                      & r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X1,k3_lattices(X0,X2,X3))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,k4_lattices(X0,X3,X1),X2))
                    & r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X1,k3_lattices(X0,X3,X2)))
                    & r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,k4_lattices(X0,X1,X3),X2))
                    & r3_lattices(X0,k4_filter_0(X0,X1,X2),k4_filter_0(X0,X1,k3_lattices(X0,X2,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t56_filter_1.p',t56_filter_1)).

fof(f248,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f109,f246])).

fof(f109,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f241,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f108,f239])).

fof(f108,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f234,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f107,f232])).

fof(f107,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f199,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f113,f197])).

fof(f113,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f192,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f112,f190])).

fof(f112,plain,(
    v3_filter_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f185,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f111,f183])).

fof(f111,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f178,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f110,f176])).

fof(f110,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
