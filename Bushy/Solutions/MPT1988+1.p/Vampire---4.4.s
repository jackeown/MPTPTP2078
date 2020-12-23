%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_7__t37_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:06 EDT 2019

% Result     : Theorem 42.30s
% Output     : Refutation 42.30s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 531 expanded)
%              Number of leaves         :   56 ( 273 expanded)
%              Depth                    :   10
%              Number of atoms          :  986 (2586 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f143,f150,f157,f164,f171,f178,f185,f192,f207,f227,f243,f259,f275,f414,f453,f462,f1526,f1578,f1628,f1635,f1642,f1649,f9665,f9672,f18740,f78034,f78055,f98235])).

fof(f98235,plain,
    ( ~ spl10_1887
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_306
    | ~ spl10_334
    | ~ spl10_336
    | ~ spl10_3514
    | spl10_11519
    | spl10_11523 ),
    inference(avatar_split_clause,[],[f98234,f78053,f78032,f18193,f1647,f1640,f1524,f155,f148,f9667])).

fof(f9667,plain,
    ( spl10_1887
  <=> ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1887])])).

fof(f148,plain,
    ( spl10_2
  <=> v5_waybel_6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f155,plain,
    ( spl10_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f1524,plain,
    ( spl10_306
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,X0,X1),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ v5_waybel_6(X2,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_306])])).

fof(f1640,plain,
    ( spl10_334
  <=> m1_subset_1(sK2(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_334])])).

fof(f1647,plain,
    ( spl10_336
  <=> m1_subset_1(sK3(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_336])])).

fof(f18193,plain,
    ( spl10_3514
  <=> k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))) = k12_lattice3(sK0,sK3(sK0,k5_waybel_0(sK0,sK1)),sK2(sK0,k5_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3514])])).

fof(f78032,plain,
    ( spl10_11519
  <=> ~ r1_orders_2(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11519])])).

fof(f78053,plain,
    ( spl10_11523
  <=> ~ r1_orders_2(sK0,sK3(sK0,k5_waybel_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11523])])).

fof(f98234,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))),sK1)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_306
    | ~ spl10_334
    | ~ spl10_336
    | ~ spl10_3514
    | ~ spl10_11519
    | ~ spl10_11523 ),
    inference(forward_demodulation,[],[f98198,f18194])).

fof(f18194,plain,
    ( k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))) = k12_lattice3(sK0,sK3(sK0,k5_waybel_0(sK0,sK1)),sK2(sK0,k5_waybel_0(sK0,sK1)))
    | ~ spl10_3514 ),
    inference(avatar_component_clause,[],[f18193])).

fof(f98198,plain,
    ( ~ r1_orders_2(sK0,k12_lattice3(sK0,sK3(sK0,k5_waybel_0(sK0,sK1)),sK2(sK0,k5_waybel_0(sK0,sK1))),sK1)
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_306
    | ~ spl10_334
    | ~ spl10_336
    | ~ spl10_11519
    | ~ spl10_11523 ),
    inference(unit_resulting_resolution,[],[f149,f78033,f1641,f156,f1648,f78054,f1525])).

fof(f1525,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_waybel_6(X2,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,k12_lattice3(sK0,X0,X1),X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,X2) )
    | ~ spl10_306 ),
    inference(avatar_component_clause,[],[f1524])).

fof(f78054,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,k5_waybel_0(sK0,sK1)),sK1)
    | ~ spl10_11523 ),
    inference(avatar_component_clause,[],[f78053])).

fof(f1648,plain,
    ( m1_subset_1(sK3(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_336 ),
    inference(avatar_component_clause,[],[f1647])).

fof(f156,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f155])).

fof(f1641,plain,
    ( m1_subset_1(sK2(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_334 ),
    inference(avatar_component_clause,[],[f1640])).

fof(f78033,plain,
    ( ~ r1_orders_2(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK1)
    | ~ spl10_11519 ),
    inference(avatar_component_clause,[],[f78032])).

fof(f149,plain,
    ( v5_waybel_6(sK1,sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f148])).

fof(f78055,plain,
    ( ~ spl10_11523
    | ~ spl10_4
    | ~ spl10_6
    | spl10_19
    | spl10_333
    | ~ spl10_336 ),
    inference(avatar_split_clause,[],[f78039,f1647,f1633,f205,f162,f155,f78053])).

fof(f162,plain,
    ( spl10_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f205,plain,
    ( spl10_19
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f1633,plain,
    ( spl10_333
  <=> ~ r2_hidden(sK3(sK0,k5_waybel_0(sK0,sK1)),k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_333])])).

fof(f78039,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,k5_waybel_0(sK0,sK1)),sK1)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_19
    | ~ spl10_333
    | ~ spl10_336 ),
    inference(unit_resulting_resolution,[],[f206,f163,f156,f1648,f1634,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X1)
      | r2_hidden(X2,k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_hidden(X2,k5_waybel_0(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k5_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t37_waybel_7.p',t17_waybel_0)).

fof(f1634,plain,
    ( ~ r2_hidden(sK3(sK0,k5_waybel_0(sK0,sK1)),k5_waybel_0(sK0,sK1))
    | ~ spl10_333 ),
    inference(avatar_component_clause,[],[f1633])).

fof(f163,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f206,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f205])).

fof(f78034,plain,
    ( ~ spl10_11519
    | ~ spl10_4
    | ~ spl10_6
    | spl10_19
    | spl10_331
    | ~ spl10_334 ),
    inference(avatar_split_clause,[],[f78019,f1640,f1626,f205,f162,f155,f78032])).

fof(f1626,plain,
    ( spl10_331
  <=> ~ r2_hidden(sK2(sK0,k5_waybel_0(sK0,sK1)),k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_331])])).

fof(f78019,plain,
    ( ~ r1_orders_2(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK1)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_19
    | ~ spl10_331
    | ~ spl10_334 ),
    inference(unit_resulting_resolution,[],[f206,f163,f156,f1641,f1627,f112])).

fof(f1627,plain,
    ( ~ r2_hidden(sK2(sK0,k5_waybel_0(sK0,sK1)),k5_waybel_0(sK0,sK1))
    | ~ spl10_331 ),
    inference(avatar_component_clause,[],[f1626])).

fof(f18740,plain,
    ( spl10_3514
    | ~ spl10_68
    | ~ spl10_334
    | ~ spl10_336 ),
    inference(avatar_split_clause,[],[f17323,f1647,f1640,f412,f18193])).

fof(f412,plain,
    ( spl10_68
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k12_lattice3(sK0,X0,X1) = k12_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f17323,plain,
    ( k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))) = k12_lattice3(sK0,sK3(sK0,k5_waybel_0(sK0,sK1)),sK2(sK0,k5_waybel_0(sK0,sK1)))
    | ~ spl10_68
    | ~ spl10_334
    | ~ spl10_336 ),
    inference(unit_resulting_resolution,[],[f1641,f1648,f413])).

fof(f413,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k12_lattice3(sK0,X0,X1) = k12_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_68 ),
    inference(avatar_component_clause,[],[f412])).

fof(f9672,plain,
    ( spl10_18
    | ~ spl10_7
    | ~ spl10_5
    | ~ spl10_1885
    | spl10_1886
    | ~ spl10_320 ),
    inference(avatar_split_clause,[],[f9648,f1576,f9670,f9660,f152,f159,f202])).

fof(f202,plain,
    ( spl10_18
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f159,plain,
    ( spl10_7
  <=> ~ l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f152,plain,
    ( spl10_5
  <=> ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f9660,plain,
    ( spl10_1885
  <=> ~ m1_subset_1(k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1885])])).

fof(f9670,plain,
    ( spl10_1886
  <=> r1_orders_2(sK0,k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1886])])).

fof(f1576,plain,
    ( spl10_320
  <=> r2_hidden(k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_320])])).

fof(f9648,plain,
    ( r1_orders_2(sK0,k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))),sK1)
    | ~ m1_subset_1(k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_320 ),
    inference(resolution,[],[f1577,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_waybel_0(X0,X1))
      | r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f1577,plain,
    ( r2_hidden(k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,sK1))
    | ~ spl10_320 ),
    inference(avatar_component_clause,[],[f1576])).

fof(f9665,plain,
    ( spl10_1884
    | ~ spl10_26
    | ~ spl10_320 ),
    inference(avatar_split_clause,[],[f9644,f1576,f241,f9663])).

fof(f9663,plain,
    ( spl10_1884
  <=> m1_subset_1(k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1884])])).

fof(f241,plain,
    ( spl10_26
  <=> m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f9644,plain,
    ( m1_subset_1(k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | ~ spl10_26
    | ~ spl10_320 ),
    inference(unit_resulting_resolution,[],[f242,f1577,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t37_waybel_7.p',t4_subset)).

fof(f242,plain,
    ( m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f241])).

fof(f1649,plain,
    ( spl10_336
    | spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_14
    | spl10_23
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f1607,f273,f257,f241,f225,f190,f183,f176,f169,f162,f141,f1647])).

fof(f141,plain,
    ( spl10_1
  <=> ~ v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f169,plain,
    ( spl10_8
  <=> v2_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f176,plain,
    ( spl10_10
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f183,plain,
    ( spl10_12
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f190,plain,
    ( spl10_14
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f225,plain,
    ( spl10_23
  <=> ~ v1_xboole_0(k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f257,plain,
    ( spl10_30
  <=> v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f273,plain,
    ( spl10_34
  <=> v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f1607,plain,
    ( m1_subset_1(sK3(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_23
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f191,f184,f177,f170,f163,f226,f258,f274,f142,f242,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & ~ r2_hidden(sK2(X0,X1),X1)
                & r2_hidden(k12_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f78,f80,f79])).

fof(f79,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X2,X1)
              & r2_hidden(k12_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & ~ r2_hidden(sK2(X0,X1),X1)
            & r2_hidden(k12_lattice3(X0,sK2(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & ~ r2_hidden(X2,X1)
          & r2_hidden(k12_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & ~ r2_hidden(X2,X1)
        & r2_hidden(k12_lattice3(X0,X2,sK3(X0,X1)),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | r2_hidden(X4,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_waybel_7(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & ~ r2_hidden(X2,X1)
                      & r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | r2_hidden(X2,X1)
                      | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v1_waybel_7(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | r2_hidden(X2,X1)
                    | ~ r2_hidden(k12_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v12_waybel_0(X1,X0)
          | ~ v1_waybel_0(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v12_waybel_0(X1,X0)
            & v1_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_waybel_7(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r2_hidden(X3,X1)
                        & ~ r2_hidden(X2,X1)
                        & r2_hidden(k12_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t37_waybel_7.p',d1_waybel_7)).

fof(f142,plain,
    ( ~ v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f274,plain,
    ( v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f273])).

fof(f258,plain,
    ( v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f257])).

fof(f226,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f225])).

fof(f170,plain,
    ( v2_lattice3(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f169])).

fof(f177,plain,
    ( v5_orders_2(sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f184,plain,
    ( v4_orders_2(sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f183])).

fof(f191,plain,
    ( v3_orders_2(sK0)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f190])).

fof(f1642,plain,
    ( spl10_334
    | spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_14
    | spl10_23
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f1608,f273,f257,f241,f225,f190,f183,f176,f169,f162,f141,f1640])).

fof(f1608,plain,
    ( m1_subset_1(sK2(sK0,k5_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_23
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f191,f184,f177,f170,f163,f226,f258,f274,f142,f242,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f1635,plain,
    ( ~ spl10_333
    | spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_14
    | spl10_23
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f1609,f273,f257,f241,f225,f190,f183,f176,f169,f162,f141,f1633])).

fof(f1609,plain,
    ( ~ r2_hidden(sK3(sK0,k5_waybel_0(sK0,sK1)),k5_waybel_0(sK0,sK1))
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_23
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f191,f184,f177,f170,f163,f226,f258,f274,f142,f242,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f1628,plain,
    ( ~ spl10_331
    | spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_14
    | spl10_23
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f1610,f273,f257,f241,f225,f190,f183,f176,f169,f162,f141,f1626])).

fof(f1610,plain,
    ( ~ r2_hidden(sK2(sK0,k5_waybel_0(sK0,sK1)),k5_waybel_0(sK0,sK1))
    | ~ spl10_1
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_14
    | ~ spl10_23
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(unit_resulting_resolution,[],[f191,f184,f177,f170,f163,f226,f258,f274,f142,f242,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | v1_waybel_7(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f1578,plain,
    ( ~ spl10_27
    | ~ spl10_35
    | ~ spl10_31
    | spl10_22
    | spl10_320
    | spl10_1
    | ~ spl10_80 ),
    inference(avatar_split_clause,[],[f1571,f460,f141,f1576,f222,f254,f270,f238])).

fof(f238,plain,
    ( spl10_27
  <=> ~ m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f270,plain,
    ( spl10_35
  <=> ~ v12_waybel_0(k5_waybel_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f254,plain,
    ( spl10_31
  <=> ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f222,plain,
    ( spl10_22
  <=> v1_xboole_0(k5_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f460,plain,
    ( spl10_80
  <=> ! [X0] :
        ( r2_hidden(k12_lattice3(sK0,sK2(sK0,X0),sK3(sK0,X0)),X0)
        | v1_waybel_7(X0,sK0)
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ v12_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f1571,plain,
    ( r2_hidden(k12_lattice3(sK0,sK2(sK0,k5_waybel_0(sK0,sK1)),sK3(sK0,k5_waybel_0(sK0,sK1))),k5_waybel_0(sK0,sK1))
    | v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_1
    | ~ spl10_80 ),
    inference(resolution,[],[f461,f142])).

fof(f461,plain,
    ( ! [X0] :
        ( v1_waybel_7(X0,sK0)
        | r2_hidden(k12_lattice3(sK0,sK2(sK0,X0),sK3(sK0,X0)),X0)
        | v1_xboole_0(X0)
        | ~ v1_waybel_0(X0,sK0)
        | ~ v12_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_80 ),
    inference(avatar_component_clause,[],[f460])).

fof(f1526,plain,
    ( spl10_18
    | ~ spl10_7
    | spl10_306
    | ~ spl10_78 ),
    inference(avatar_split_clause,[],[f1512,f451,f1524,f159,f202])).

fof(f451,plain,
    ( spl10_78
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f1512,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,X0,X1),X2)
        | r1_orders_2(sK0,X0,X2)
        | r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_waybel_6(X2,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_78 ),
    inference(duplicate_literal_removal,[],[f1509])).

fof(f1509,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,k12_lattice3(sK0,X0,X1),X2)
        | r1_orders_2(sK0,X0,X2)
        | r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v5_waybel_6(X2,sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_78 ),
    inference(superposition,[],[f113,f452])).

fof(f452,plain,
    ( ! [X0,X1] :
        ( k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_78 ),
    inference(avatar_component_clause,[],[f451])).

fof(f113,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
      | r1_orders_2(X0,X4,X1)
      | r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v5_waybel_6(X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ( ~ r1_orders_2(X0,sK5(X0,X1),X1)
                & ~ r1_orders_2(X0,sK4(X0,X1),X1)
                & r1_orders_2(X0,k11_lattice3(X0,sK4(X0,X1),sK5(X0,X1)),X1)
                & m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X1)
                      | r1_orders_2(X0,X4,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f84,f86,f85])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(X0,X3,X1)
              & ~ r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r1_orders_2(X0,X3,X1)
            & ~ r1_orders_2(X0,sK4(X0,X1),X1)
            & r1_orders_2(X0,k11_lattice3(X0,sK4(X0,X1),X3),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & ~ r1_orders_2(X0,X2,X1)
          & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1),X1)
        & ~ r1_orders_2(X0,X2,X1)
        & r1_orders_2(X0,k11_lattice3(X0,X2,sK5(X0,X1)),X1)
        & m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X1)
                      & ~ r1_orders_2(X0,X2,X1)
                      & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r1_orders_2(X0,X5,X1)
                      | r1_orders_2(X0,X4,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X4,X5),X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_waybel_6(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r1_orders_2(X0,X3,X1)
                      & ~ r1_orders_2(X0,X2,X1)
                      & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r1_orders_2(X0,X3,X1)
                      | r1_orders_2(X0,X2,X1)
                      | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v5_waybel_6(X1,X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | r1_orders_2(X0,X2,X1)
                    | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X1)
                    | r1_orders_2(X0,X2,X1)
                    | ~ r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ~ r1_orders_2(X0,X3,X1)
                        & ~ r1_orders_2(X0,X2,X1)
                        & r1_orders_2(X0,k11_lattice3(X0,X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t37_waybel_7.p',d6_waybel_6)).

fof(f462,plain,
    ( ~ spl10_15
    | ~ spl10_13
    | ~ spl10_11
    | ~ spl10_7
    | spl10_80
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f458,f169,f460,f159,f173,f180,f187])).

fof(f187,plain,
    ( spl10_15
  <=> ~ v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f180,plain,
    ( spl10_13
  <=> ~ v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f173,plain,
    ( spl10_11
  <=> ~ v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f458,plain,
    ( ! [X0] :
        ( r2_hidden(k12_lattice3(sK0,sK2(sK0,X0),sK3(sK0,X0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v12_waybel_0(X0,sK0)
        | ~ v1_waybel_0(X0,sK0)
        | v1_xboole_0(X0)
        | ~ l1_orders_2(sK0)
        | v1_waybel_7(X0,sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f104,f170])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v2_lattice3(X0)
      | r2_hidden(k12_lattice3(X0,sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v12_waybel_0(X1,X0)
      | ~ v1_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_orders_2(X0)
      | v1_waybel_7(X1,X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f453,plain,
    ( ~ spl10_11
    | ~ spl10_7
    | spl10_78
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f420,f169,f451,f159,f173])).

fof(f420,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | k12_lattice3(sK0,X1,X0) = k11_lattice3(sK0,X1,X0)
        | ~ v5_orders_2(sK0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f126,f170])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t37_waybel_7.p',redefinition_k12_lattice3)).

fof(f414,plain,
    ( ~ spl10_11
    | ~ spl10_7
    | spl10_68
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f402,f169,f412,f159,f173])).

fof(f402,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | k12_lattice3(sK0,X0,X1) = k12_lattice3(sK0,X1,X0)
        | ~ v5_orders_2(sK0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f125,f170])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k12_lattice3(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t37_waybel_7.p',commutativity_k12_lattice3)).

fof(f275,plain,
    ( spl10_34
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_12
    | spl10_19 ),
    inference(avatar_split_clause,[],[f260,f205,f183,f162,f155,f273])).

fof(f260,plain,
    ( v12_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_12
    | ~ spl10_19 ),
    inference(unit_resulting_resolution,[],[f206,f184,f163,f156,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => v12_waybel_0(k5_waybel_0(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t37_waybel_7.p',fc12_waybel_0)).

fof(f259,plain,
    ( spl10_30
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_14
    | spl10_19 ),
    inference(avatar_split_clause,[],[f244,f205,f190,f162,f155,f257])).

fof(f244,plain,
    ( v1_waybel_0(k5_waybel_0(sK0,sK1),sK0)
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_19 ),
    inference(unit_resulting_resolution,[],[f206,f191,f163,f156,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_waybel_0(k5_waybel_0(X0,X1),X0)
        & ~ v1_xboole_0(k5_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t37_waybel_7.p',fc8_waybel_0)).

fof(f243,plain,
    ( spl10_26
    | ~ spl10_4
    | ~ spl10_6
    | spl10_19 ),
    inference(avatar_split_clause,[],[f228,f205,f162,f155,f241])).

fof(f228,plain,
    ( m1_subset_1(k5_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_19 ),
    inference(unit_resulting_resolution,[],[f206,f163,f156,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t37_waybel_7.p',dt_k5_waybel_0)).

fof(f227,plain,
    ( ~ spl10_23
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_14
    | spl10_19 ),
    inference(avatar_split_clause,[],[f211,f205,f190,f162,f155,f225])).

fof(f211,plain,
    ( ~ v1_xboole_0(k5_waybel_0(sK0,sK1))
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_14
    | ~ spl10_19 ),
    inference(unit_resulting_resolution,[],[f206,f191,f163,f156,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k5_waybel_0(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f207,plain,
    ( ~ spl10_19
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f200,f169,f162,f205])).

fof(f200,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f163,f170,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t37_waybel_7.p',cc2_lattice3)).

fof(f192,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f93,f190])).

fof(f93,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( ~ v1_waybel_7(k5_waybel_0(sK0,sK1),sK0)
    & v5_waybel_6(sK1,sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f75,f74])).

fof(f74,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
            & v5_waybel_6(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ~ v1_waybel_7(k5_waybel_0(sK0,X1),sK0)
          & v5_waybel_6(X1,sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v1_waybel_7(k5_waybel_0(X0,sK1),X0)
        & v5_waybel_6(sK1,X0)
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_waybel_7(k5_waybel_0(X0,X1),X0)
          & v5_waybel_6(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v5_waybel_6(X1,X0)
             => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v5_waybel_6(X1,X0)
           => v1_waybel_7(k5_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_7__t37_waybel_7.p',t37_waybel_7)).

fof(f185,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f94,f183])).

fof(f94,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f178,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f95,f176])).

fof(f95,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f171,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f96,f169])).

fof(f96,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f164,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f97,f162])).

fof(f97,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f157,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f98,f155])).

fof(f98,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f150,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f99,f148])).

fof(f99,plain,(
    v5_waybel_6(sK1,sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f143,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f100,f141])).

fof(f100,plain,(
    ~ v1_waybel_7(k5_waybel_0(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f76])).
%------------------------------------------------------------------------------
