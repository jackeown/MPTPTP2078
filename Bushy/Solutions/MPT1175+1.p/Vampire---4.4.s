%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t82_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:23 EDT 2019

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  515 (2065 expanded)
%              Number of leaves         :  140 ( 832 expanded)
%              Depth                    :   15
%              Number of atoms          : 1514 (6314 expanded)
%              Number of equality atoms :   79 ( 300 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f153,f160,f167,f174,f181,f188,f195,f202,f209,f216,f223,f230,f239,f270,f284,f301,f321,f326,f334,f398,f417,f427,f447,f467,f481,f489,f498,f517,f539,f567,f585,f592,f630,f638,f650,f654,f672,f673,f691,f700,f707,f708,f863,f1061,f1079,f1201,f1243,f1286,f1442,f1571,f1590,f1595,f1602,f1609,f1618,f1625,f1720,f1731,f1738,f1749,f1763,f1785,f1808,f1822,f1837,f1844,f1851,f1866,f1875,f1882,f1891,f1902,f1909,f1921,f1928,f1939,f1946,f1955,f1962,f1969,f1970,f1974,f1981,f2004,f2027,f2049,f2111,f2119,f2127,f2128,f2129,f2145,f2150,f2157,f2164,f2174,f2183,f2192,f2219])).

fof(f2219,plain,
    ( ~ spl10_16
    | ~ spl10_184
    | ~ spl10_194 ),
    inference(avatar_contradiction_clause,[],[f2218])).

fof(f2218,plain,
    ( $false
    | ~ spl10_16
    | ~ spl10_184
    | ~ spl10_194 ),
    inference(subsumption_resolution,[],[f2214,f201])).

fof(f201,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl10_16
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f2214,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | ~ spl10_184
    | ~ spl10_194 ),
    inference(resolution,[],[f2191,f2147])).

fof(f2147,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl10_184 ),
    inference(resolution,[],[f2144,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f62,f88])).

fof(f88,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',t3_xboole_0)).

fof(f2144,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)
    | ~ spl10_184 ),
    inference(avatar_component_clause,[],[f2143])).

fof(f2143,plain,
    ( spl10_184
  <=> r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_184])])).

fof(f2191,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3)
    | ~ spl10_194 ),
    inference(avatar_component_clause,[],[f2190])).

fof(f2190,plain,
    ( spl10_194
  <=> r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_194])])).

fof(f2192,plain,
    ( spl10_194
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f2131,f228,f221,f172,f165,f158,f151,f144,f2190])).

fof(f144,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f151,plain,
    ( spl10_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f158,plain,
    ( spl10_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f165,plain,
    ( spl10_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f172,plain,
    ( spl10_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f221,plain,
    ( spl10_22
  <=> m2_orders_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f228,plain,
    ( spl10_24
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f2131,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(resolution,[],[f1633,f222])).

fof(f222,plain,
    ( m2_orders_2(sK3,sK0,sK1)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f221])).

fof(f1633,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_24 ),
    inference(resolution,[],[f1021,f229])).

fof(f229,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f228])).

fof(f1021,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X0,sK0,X1)
        | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f1020,f145])).

fof(f145,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f144])).

fof(f1020,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
        | v2_struct_0(sK0) )
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f1019,f152])).

fof(f152,plain,
    ( v3_orders_2(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f151])).

fof(f1019,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f1018,f159])).

fof(f159,plain,
    ( v4_orders_2(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1018,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f1017,f173])).

fof(f173,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f172])).

fof(f1017,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | r2_hidden(k1_funct_1(X1,u1_struct_0(sK0)),X0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_6 ),
    inference(resolution,[],[f117,f166])).

fof(f166,plain,
    ( v5_orders_2(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',t79_orders_2)).

fof(f2183,plain,
    ( ~ spl10_193
    | ~ spl10_184 ),
    inference(avatar_split_clause,[],[f2175,f2143,f2181])).

fof(f2181,plain,
    ( spl10_193
  <=> ~ r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_193])])).

fof(f2175,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | ~ spl10_184 ),
    inference(resolution,[],[f2147,f2144])).

fof(f2174,plain,
    ( ~ spl10_191
    | ~ spl10_188 ),
    inference(avatar_split_clause,[],[f2166,f2162,f2172])).

fof(f2172,plain,
    ( spl10_191
  <=> ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_191])])).

fof(f2162,plain,
    ( spl10_188
  <=> r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_188])])).

fof(f2166,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_funct_1(sK1,u1_struct_0(sK0)))
    | ~ spl10_188 ),
    inference(resolution,[],[f2163,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',antisymmetry_r2_hidden)).

fof(f2163,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_188 ),
    inference(avatar_component_clause,[],[f2162])).

fof(f2164,plain,
    ( spl10_188
    | ~ spl10_100
    | ~ spl10_184 ),
    inference(avatar_split_clause,[],[f2146,f2143,f1569,f2162])).

fof(f1569,plain,
    ( spl10_100
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f2146,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_100
    | ~ spl10_184 ),
    inference(resolution,[],[f2144,f1570])).

fof(f1570,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl10_100 ),
    inference(avatar_component_clause,[],[f1569])).

fof(f2157,plain,
    ( ~ spl10_187
    | ~ spl10_184 ),
    inference(avatar_split_clause,[],[f2148,f2143,f2155])).

fof(f2155,plain,
    ( spl10_187
  <=> ~ r2_hidden(sK2,k1_funct_1(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_187])])).

fof(f2148,plain,
    ( ~ r2_hidden(sK2,k1_funct_1(sK1,u1_struct_0(sK0)))
    | ~ spl10_184 ),
    inference(resolution,[],[f2144,f124])).

fof(f2150,plain,
    ( ~ spl10_103
    | ~ spl10_184 ),
    inference(avatar_split_clause,[],[f2149,f2143,f1579])).

fof(f1579,plain,
    ( spl10_103
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_103])])).

fof(f2149,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_184 ),
    inference(resolution,[],[f2144,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',t7_boole)).

fof(f2145,plain,
    ( spl10_184
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f2130,f228,f214,f172,f165,f158,f151,f144,f2143])).

fof(f214,plain,
    ( spl10_20
  <=> m2_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f2130,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(resolution,[],[f1633,f215])).

fof(f215,plain,
    ( m2_orders_2(sK2,sK0,sK1)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f214])).

fof(f2129,plain,
    ( spl10_182
    | spl10_180
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_100 ),
    inference(avatar_split_clause,[],[f1652,f1569,f282,f268,f193,f2117,f2125])).

fof(f2125,plain,
    ( spl10_182
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_182])])).

fof(f2117,plain,
    ( spl10_180
  <=> r1_xboole_0(k1_zfmisc_1(k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_180])])).

fof(f193,plain,
    ( spl10_14
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f268,plain,
    ( spl10_28
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f282,plain,
    ( spl10_30
  <=> k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f1652,plain,
    ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),sK2)
    | k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_100 ),
    inference(resolution,[],[f1649,f789])).

fof(f789,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0)
        | k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),X0) )
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(forward_demodulation,[],[f783,f283])).

fof(f283,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f282])).

fof(f783,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0)
        | sK5(k1_zfmisc_1(k1_xboole_0)) = sK6(k1_zfmisc_1(k1_xboole_0),X0) )
    | ~ spl10_14
    | ~ spl10_28 ),
    inference(resolution,[],[f780,f274])).

fof(f274,plain,
    ( ! [X4] :
        ( ~ v1_xboole_0(X4)
        | sK5(k1_zfmisc_1(k1_xboole_0)) = X4 )
    | ~ spl10_28 ),
    inference(resolution,[],[f269,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',t8_boole)).

fof(f269,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f268])).

fof(f780,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK6(k1_zfmisc_1(k1_xboole_0),X0))
        | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0) )
    | ~ spl10_14 ),
    inference(resolution,[],[f304,f250])).

fof(f250,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f126,f119])).

fof(f119,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f26,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',existence_m1_subset_1)).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',t2_subset)).

fof(f304,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK6(k1_zfmisc_1(k1_xboole_0),X1))
        | r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X1) )
    | ~ spl10_14 ),
    inference(resolution,[],[f260,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f260,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X2) )
    | ~ spl10_14 ),
    inference(resolution,[],[f258,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',t1_subset)).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl10_14 ),
    inference(resolution,[],[f134,f194])).

fof(f194,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f193])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',t5_subset)).

fof(f1649,plain,
    ( ! [X1] :
        ( ~ r1_xboole_0(X1,u1_struct_0(sK0))
        | r1_xboole_0(X1,sK2) )
    | ~ spl10_100 ),
    inference(duplicate_literal_removal,[],[f1645])).

fof(f1645,plain,
    ( ! [X1] :
        ( r1_xboole_0(X1,sK2)
        | ~ r1_xboole_0(X1,u1_struct_0(sK0))
        | r1_xboole_0(X1,sK2) )
    | ~ spl10_100 ),
    inference(resolution,[],[f1576,f255])).

fof(f255,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X2)
      | ~ r1_xboole_0(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f122,f120])).

fof(f1576,plain,
    ( ! [X1] :
        ( r2_hidden(sK6(X1,sK2),u1_struct_0(sK0))
        | r1_xboole_0(X1,sK2) )
    | ~ spl10_100 ),
    inference(resolution,[],[f1570,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f2128,plain,
    ( spl10_176
    | spl10_180
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_100 ),
    inference(avatar_split_clause,[],[f1651,f1569,f282,f268,f193,f2117,f2103])).

fof(f2103,plain,
    ( spl10_176
  <=> k1_xboole_0 = sK6(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_176])])).

fof(f1651,plain,
    ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),sK2)
    | k1_xboole_0 = sK6(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_100 ),
    inference(resolution,[],[f1649,f1269])).

fof(f1269,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0)
        | k1_xboole_0 = sK6(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(resolution,[],[f799,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',symmetry_r1_xboole_0)).

fof(f799,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = sK6(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30 ),
    inference(forward_demodulation,[],[f793,f283])).

fof(f793,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,k1_zfmisc_1(k1_xboole_0))
        | sK5(k1_zfmisc_1(k1_xboole_0)) = sK6(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl10_14
    | ~ spl10_28 ),
    inference(resolution,[],[f790,f274])).

fof(f790,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK6(X0,k1_zfmisc_1(k1_xboole_0)))
        | r1_xboole_0(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl10_14 ),
    inference(resolution,[],[f305,f250])).

fof(f305,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,sK6(X3,k1_zfmisc_1(k1_xboole_0)))
        | r1_xboole_0(X3,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl10_14 ),
    inference(resolution,[],[f260,f121])).

fof(f2127,plain,
    ( spl10_182
    | spl10_178
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_100 ),
    inference(avatar_split_clause,[],[f1636,f1569,f282,f268,f193,f2109,f2125])).

fof(f2109,plain,
    ( spl10_178
  <=> r1_xboole_0(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_178])])).

fof(f1636,plain,
    ( r1_xboole_0(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_100 ),
    inference(resolution,[],[f1632,f789])).

fof(f1632,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,u1_struct_0(sK0))
        | r1_xboole_0(sK2,X0) )
    | ~ spl10_100 ),
    inference(duplicate_literal_removal,[],[f1626])).

fof(f1626,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK2,X0)
        | ~ r1_xboole_0(X0,u1_struct_0(sK0))
        | r1_xboole_0(sK2,X0) )
    | ~ spl10_100 ),
    inference(resolution,[],[f1575,f256])).

fof(f256,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK6(X3,X4),X5)
      | ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f122,f121])).

fof(f1575,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(sK2,X0),u1_struct_0(sK0))
        | r1_xboole_0(sK2,X0) )
    | ~ spl10_100 ),
    inference(resolution,[],[f1570,f120])).

fof(f2119,plain,
    ( spl10_180
    | ~ spl10_178 ),
    inference(avatar_split_clause,[],[f2112,f2109,f2117])).

fof(f2112,plain,
    ( r1_xboole_0(k1_zfmisc_1(k1_xboole_0),sK2)
    | ~ spl10_178 ),
    inference(resolution,[],[f2110,f123])).

fof(f2110,plain,
    ( r1_xboole_0(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_178 ),
    inference(avatar_component_clause,[],[f2109])).

fof(f2111,plain,
    ( spl10_176
    | spl10_178
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_100 ),
    inference(avatar_split_clause,[],[f1635,f1569,f282,f268,f193,f2109,f2103])).

fof(f1635,plain,
    ( r1_xboole_0(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK6(u1_struct_0(sK0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_100 ),
    inference(resolution,[],[f1632,f1269])).

fof(f2049,plain,
    ( spl10_174
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | spl10_145 ),
    inference(avatar_split_clause,[],[f1884,f1880,f282,f268,f193,f2047])).

fof(f2047,plain,
    ( spl10_174
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_174])])).

fof(f1880,plain,
    ( spl10_145
  <=> ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_145])])).

fof(f1884,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_145 ),
    inference(resolution,[],[f1881,f789])).

fof(f1881,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl10_145 ),
    inference(avatar_component_clause,[],[f1880])).

fof(f2027,plain,
    ( spl10_172
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | spl10_145 ),
    inference(avatar_split_clause,[],[f1883,f1880,f282,f268,f193,f2025])).

fof(f2025,plain,
    ( spl10_172
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_172])])).

fof(f1883,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_145 ),
    inference(resolution,[],[f1881,f1269])).

fof(f2004,plain,
    ( spl10_170
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | spl10_139 ),
    inference(avatar_split_clause,[],[f1853,f1849,f282,f268,f193,f2002])).

fof(f2002,plain,
    ( spl10_170
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),k1_orders_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_170])])).

fof(f1849,plain,
    ( spl10_139
  <=> ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_orders_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_139])])).

fof(f1853,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),k1_orders_1(sK2))
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_139 ),
    inference(resolution,[],[f1850,f789])).

fof(f1850,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_orders_1(sK2))
    | ~ spl10_139 ),
    inference(avatar_component_clause,[],[f1849])).

fof(f1981,plain,
    ( spl10_168
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | spl10_139 ),
    inference(avatar_split_clause,[],[f1852,f1849,f282,f268,f193,f1979])).

fof(f1979,plain,
    ( spl10_168
  <=> k1_xboole_0 = sK6(k1_orders_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_168])])).

fof(f1852,plain,
    ( k1_xboole_0 = sK6(k1_orders_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_139 ),
    inference(resolution,[],[f1850,f1269])).

fof(f1974,plain,
    ( spl10_132
    | spl10_166
    | ~ spl10_128 ),
    inference(avatar_split_clause,[],[f1795,f1783,f1972,f1814])).

fof(f1814,plain,
    ( spl10_132
  <=> v1_xboole_0(k1_orders_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_132])])).

fof(f1972,plain,
    ( spl10_166
  <=> ! [X1] :
        ( ~ r2_hidden(k1_xboole_0,X1)
        | ~ r1_xboole_0(k1_orders_1(sK2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_166])])).

fof(f1783,plain,
    ( spl10_128
  <=> k1_xboole_0 = sK5(k1_orders_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_128])])).

fof(f1795,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k1_xboole_0,X1)
        | ~ r1_xboole_0(k1_orders_1(sK2),X1)
        | v1_xboole_0(k1_orders_1(sK2)) )
    | ~ spl10_128 ),
    inference(superposition,[],[f257,f1784])).

fof(f1784,plain,
    ( k1_xboole_0 = sK5(k1_orders_1(sK2))
    | ~ spl10_128 ),
    inference(avatar_component_clause,[],[f1783])).

fof(f257,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(sK5(X6),X7)
      | ~ r1_xboole_0(X6,X7)
      | v1_xboole_0(X6) ) ),
    inference(resolution,[],[f122,f250])).

fof(f1970,plain,
    ( spl10_132
    | spl10_142
    | spl10_140
    | ~ spl10_128 ),
    inference(avatar_split_clause,[],[f1789,f1783,f1858,f1864,f1814])).

fof(f1864,plain,
    ( spl10_142
  <=> v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_142])])).

fof(f1858,plain,
    ( spl10_140
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_140])])).

fof(f1789,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_orders_1(sK2))
    | ~ spl10_128 ),
    inference(superposition,[],[f386,f1784])).

fof(f386,plain,(
    ! [X4] :
      ( r2_hidden(sK5(k1_orders_1(X4)),k1_zfmisc_1(X4))
      | v1_xboole_0(k1_zfmisc_1(X4))
      | v1_xboole_0(k1_orders_1(X4)) ) ),
    inference(resolution,[],[f380,f126])).

fof(f380,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(k1_orders_1(X0)),k1_zfmisc_1(X0))
      | v1_xboole_0(k1_orders_1(X0)) ) ),
    inference(resolution,[],[f378,f250])).

fof(f378,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_orders_1(X1))
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f377,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',t4_subset)).

fof(f377,plain,(
    ! [X0] : m1_subset_1(k1_orders_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(subsumption_resolution,[],[f374,f139])).

fof(f139,plain,(
    ! [X0] : m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(forward_demodulation,[],[f110,f109])).

fof(f109,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',redefinition_k9_setfam_1)).

fof(f110,plain,(
    ! [X0] : m1_subset_1(k9_setfam_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k9_setfam_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',dt_k9_setfam_1)).

fof(f374,plain,(
    ! [X0] :
      ( m1_subset_1(k1_orders_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f131,f137])).

fof(f137,plain,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(X0),k1_tarski(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f111,f109])).

fof(f111,plain,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',d2_orders_1)).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',dt_k7_subset_1)).

fof(f1969,plain,
    ( ~ spl10_165
    | ~ spl10_58
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f1930,f1858,f509,f1967])).

fof(f1967,plain,
    ( spl10_165
  <=> ~ r1_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_165])])).

fof(f509,plain,
    ( spl10_58
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f1930,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_58
    | ~ spl10_140 ),
    inference(resolution,[],[f1871,f510])).

fof(f510,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_58 ),
    inference(avatar_component_clause,[],[f509])).

fof(f1871,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_xboole_0,X2)
        | ~ r1_xboole_0(k1_zfmisc_1(sK2),X2) )
    | ~ spl10_140 ),
    inference(resolution,[],[f1859,f122])).

fof(f1859,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl10_140 ),
    inference(avatar_component_clause,[],[f1858])).

fof(f1962,plain,
    ( ~ spl10_163
    | ~ spl10_58
    | ~ spl10_136 ),
    inference(avatar_split_clause,[],[f1893,f1835,f509,f1960])).

fof(f1960,plain,
    ( spl10_163
  <=> ~ r1_xboole_0(k1_orders_1(sK2),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_163])])).

fof(f1835,plain,
    ( spl10_136
  <=> r2_hidden(k1_xboole_0,k1_orders_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_136])])).

fof(f1893,plain,
    ( ~ r1_xboole_0(k1_orders_1(sK2),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_58
    | ~ spl10_136 ),
    inference(resolution,[],[f1841,f510])).

fof(f1841,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | ~ r1_xboole_0(k1_orders_1(sK2),X0) )
    | ~ spl10_136 ),
    inference(resolution,[],[f1836,f122])).

fof(f1836,plain,
    ( r2_hidden(k1_xboole_0,k1_orders_1(sK2))
    | ~ spl10_136 ),
    inference(avatar_component_clause,[],[f1835])).

fof(f1955,plain,
    ( ~ spl10_161
    | ~ spl10_136
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f1932,f1858,f1835,f1953])).

fof(f1953,plain,
    ( spl10_161
  <=> ~ r1_xboole_0(k1_zfmisc_1(sK2),k1_orders_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_161])])).

fof(f1932,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(sK2),k1_orders_1(sK2))
    | ~ spl10_136
    | ~ spl10_140 ),
    inference(resolution,[],[f1871,f1836])).

fof(f1946,plain,
    ( ~ spl10_159
    | ~ spl10_36
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f1929,f1858,f319,f1944])).

fof(f1944,plain,
    ( spl10_159
  <=> ~ r1_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_159])])).

fof(f319,plain,
    ( spl10_36
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f1929,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_36
    | ~ spl10_140 ),
    inference(resolution,[],[f1871,f320])).

fof(f320,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f319])).

fof(f1939,plain,
    ( ~ spl10_157
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f1931,f1858,f1937])).

fof(f1937,plain,
    ( spl10_157
  <=> ~ r1_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_157])])).

fof(f1931,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(sK2),k1_zfmisc_1(sK2))
    | ~ spl10_140 ),
    inference(resolution,[],[f1871,f1859])).

fof(f1928,plain,
    ( ~ spl10_155
    | ~ spl10_58
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f1867,f1858,f509,f1926])).

fof(f1926,plain,
    ( spl10_155
  <=> ~ r1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_155])])).

fof(f1867,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(sK2))
    | ~ spl10_58
    | ~ spl10_140 ),
    inference(resolution,[],[f1859,f680])).

fof(f680,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k1_xboole_0,X1)
        | ~ r1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),X1) )
    | ~ spl10_58 ),
    inference(resolution,[],[f510,f122])).

fof(f1921,plain,
    ( ~ spl10_153
    | ~ spl10_136
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f1894,f1858,f1835,f1919])).

fof(f1919,plain,
    ( spl10_153
  <=> ~ r1_xboole_0(k1_orders_1(sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_153])])).

fof(f1894,plain,
    ( ~ r1_xboole_0(k1_orders_1(sK2),k1_zfmisc_1(sK2))
    | ~ spl10_136
    | ~ spl10_140 ),
    inference(resolution,[],[f1841,f1859])).

fof(f1909,plain,
    ( ~ spl10_151
    | ~ spl10_36
    | ~ spl10_136 ),
    inference(avatar_split_clause,[],[f1892,f1835,f319,f1907])).

fof(f1907,plain,
    ( spl10_151
  <=> ~ r1_xboole_0(k1_orders_1(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_151])])).

fof(f1892,plain,
    ( ~ r1_xboole_0(k1_orders_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_36
    | ~ spl10_136 ),
    inference(resolution,[],[f1841,f320])).

fof(f1902,plain,
    ( ~ spl10_149
    | ~ spl10_136 ),
    inference(avatar_split_clause,[],[f1895,f1835,f1900])).

fof(f1900,plain,
    ( spl10_149
  <=> ~ r1_xboole_0(k1_orders_1(sK2),k1_orders_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_149])])).

fof(f1895,plain,
    ( ~ r1_xboole_0(k1_orders_1(sK2),k1_orders_1(sK2))
    | ~ spl10_136 ),
    inference(resolution,[],[f1841,f1836])).

fof(f1891,plain,
    ( ~ spl10_147
    | ~ spl10_58
    | ~ spl10_136 ),
    inference(avatar_split_clause,[],[f1838,f1835,f509,f1889])).

fof(f1889,plain,
    ( spl10_147
  <=> ~ r1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_orders_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_147])])).

fof(f1838,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_orders_1(sK2))
    | ~ spl10_58
    | ~ spl10_136 ),
    inference(resolution,[],[f1836,f680])).

fof(f1882,plain,
    ( ~ spl10_145
    | ~ spl10_36
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f1868,f1858,f319,f1880])).

fof(f1868,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK2))
    | ~ spl10_36
    | ~ spl10_140 ),
    inference(resolution,[],[f1859,f676])).

fof(f676,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k1_xboole_0,X2)
        | ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X2) )
    | ~ spl10_36 ),
    inference(resolution,[],[f320,f122])).

fof(f1875,plain,
    ( ~ spl10_143
    | ~ spl10_140 ),
    inference(avatar_split_clause,[],[f1873,f1858,f1861])).

fof(f1861,plain,
    ( spl10_143
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_143])])).

fof(f1873,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | ~ spl10_140 ),
    inference(resolution,[],[f1859,f130])).

fof(f1866,plain,
    ( spl10_140
    | spl10_142
    | ~ spl10_134 ),
    inference(avatar_split_clause,[],[f1825,f1820,f1864,f1858])).

fof(f1820,plain,
    ( spl10_134
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f1825,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl10_134 ),
    inference(resolution,[],[f1821,f126])).

fof(f1821,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | ~ spl10_134 ),
    inference(avatar_component_clause,[],[f1820])).

fof(f1851,plain,
    ( ~ spl10_139
    | ~ spl10_36
    | ~ spl10_136 ),
    inference(avatar_split_clause,[],[f1839,f1835,f319,f1849])).

fof(f1839,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_orders_1(sK2))
    | ~ spl10_36
    | ~ spl10_136 ),
    inference(resolution,[],[f1836,f676])).

fof(f1844,plain,
    ( ~ spl10_133
    | ~ spl10_136 ),
    inference(avatar_split_clause,[],[f1843,f1835,f1811])).

fof(f1811,plain,
    ( spl10_133
  <=> ~ v1_xboole_0(k1_orders_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_133])])).

fof(f1843,plain,
    ( ~ v1_xboole_0(k1_orders_1(sK2))
    | ~ spl10_136 ),
    inference(resolution,[],[f1836,f130])).

fof(f1837,plain,
    ( spl10_132
    | spl10_136
    | ~ spl10_128 ),
    inference(avatar_split_clause,[],[f1797,f1783,f1835,f1814])).

fof(f1797,plain,
    ( r2_hidden(k1_xboole_0,k1_orders_1(sK2))
    | v1_xboole_0(k1_orders_1(sK2))
    | ~ spl10_128 ),
    inference(superposition,[],[f250,f1784])).

fof(f1822,plain,
    ( spl10_132
    | spl10_134
    | ~ spl10_128 ),
    inference(avatar_split_clause,[],[f1787,f1783,f1820,f1814])).

fof(f1787,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2))
    | v1_xboole_0(k1_orders_1(sK2))
    | ~ spl10_128 ),
    inference(superposition,[],[f380,f1784])).

fof(f1808,plain,
    ( spl10_130
    | ~ spl10_128 ),
    inference(avatar_split_clause,[],[f1798,f1783,f1806])).

fof(f1806,plain,
    ( spl10_130
  <=> m1_subset_1(k1_xboole_0,k1_orders_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_130])])).

fof(f1798,plain,
    ( m1_subset_1(k1_xboole_0,k1_orders_1(sK2))
    | ~ spl10_128 ),
    inference(superposition,[],[f119,f1784])).

fof(f1785,plain,
    ( spl10_128
    | ~ spl10_124 ),
    inference(avatar_split_clause,[],[f1764,f1755,f1783])).

fof(f1755,plain,
    ( spl10_124
  <=> v1_xboole_0(sK5(k1_orders_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_124])])).

fof(f1764,plain,
    ( k1_xboole_0 = sK5(k1_orders_1(sK2))
    | ~ spl10_124 ),
    inference(resolution,[],[f1756,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',t6_boole)).

fof(f1756,plain,
    ( v1_xboole_0(sK5(k1_orders_1(sK2)))
    | ~ spl10_124 ),
    inference(avatar_component_clause,[],[f1755])).

fof(f1763,plain,
    ( spl10_124
    | spl10_102
    | spl10_126
    | ~ spl10_100 ),
    inference(avatar_split_clause,[],[f1574,f1569,f1761,f1582,f1755])).

fof(f1582,plain,
    ( spl10_102
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f1761,plain,
    ( spl10_126
  <=> r2_hidden(sK5(sK5(k1_orders_1(sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_126])])).

fof(f1574,plain,
    ( r2_hidden(sK5(sK5(k1_orders_1(sK2))),u1_struct_0(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK5(k1_orders_1(sK2)))
    | ~ spl10_100 ),
    inference(resolution,[],[f1570,f1309])).

fof(f1309,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK5(k1_orders_1(X0))),X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK5(k1_orders_1(X0))) ) ),
    inference(subsumption_resolution,[],[f1302,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_orders_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_orders_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k1_orders_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',fc1_orders_1)).

fof(f1302,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_orders_1(X0))
      | v1_xboole_0(sK5(k1_orders_1(X0)))
      | v1_xboole_0(X0)
      | r2_hidden(sK5(sK5(k1_orders_1(X0))),X0) ) ),
    inference(resolution,[],[f839,f126])).

fof(f839,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK5(k1_orders_1(X0))),X0)
      | v1_xboole_0(k1_orders_1(X0))
      | v1_xboole_0(sK5(k1_orders_1(X0))) ) ),
    inference(resolution,[],[f384,f250])).

fof(f384,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,sK5(k1_orders_1(X1)))
      | m1_subset_1(X2,X1)
      | v1_xboole_0(k1_orders_1(X1)) ) ),
    inference(resolution,[],[f380,f133])).

fof(f1749,plain,
    ( spl10_114
    | ~ spl10_123
    | ~ spl10_116 ),
    inference(avatar_split_clause,[],[f1741,f1718,f1747,f1712])).

fof(f1712,plain,
    ( spl10_114
  <=> v1_xboole_0(sK5(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_114])])).

fof(f1747,plain,
    ( spl10_123
  <=> ~ r1_xboole_0(u1_struct_0(sK0),sK5(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_123])])).

fof(f1718,plain,
    ( spl10_116
  <=> r2_hidden(sK5(sK5(k1_zfmisc_1(sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).

fof(f1741,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK0),sK5(k1_zfmisc_1(sK2)))
    | v1_xboole_0(sK5(k1_zfmisc_1(sK2)))
    | ~ spl10_116 ),
    inference(resolution,[],[f1722,f250])).

fof(f1722,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK5(k1_zfmisc_1(sK2))),X0)
        | ~ r1_xboole_0(u1_struct_0(sK0),X0) )
    | ~ spl10_116 ),
    inference(resolution,[],[f1719,f122])).

fof(f1719,plain,
    ( r2_hidden(sK5(sK5(k1_zfmisc_1(sK2))),u1_struct_0(sK0))
    | ~ spl10_116 ),
    inference(avatar_component_clause,[],[f1718])).

fof(f1738,plain,
    ( spl10_114
    | ~ spl10_121
    | ~ spl10_116 ),
    inference(avatar_split_clause,[],[f1721,f1718,f1736,f1712])).

fof(f1736,plain,
    ( spl10_121
  <=> ~ r1_xboole_0(sK5(k1_zfmisc_1(sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_121])])).

fof(f1721,plain,
    ( ~ r1_xboole_0(sK5(k1_zfmisc_1(sK2)),u1_struct_0(sK0))
    | v1_xboole_0(sK5(k1_zfmisc_1(sK2)))
    | ~ spl10_116 ),
    inference(resolution,[],[f1719,f257])).

fof(f1731,plain,
    ( ~ spl10_119
    | ~ spl10_116 ),
    inference(avatar_split_clause,[],[f1723,f1718,f1729])).

fof(f1729,plain,
    ( spl10_119
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK5(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_119])])).

fof(f1723,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK5(k1_zfmisc_1(sK2))))
    | ~ spl10_116 ),
    inference(resolution,[],[f1719,f124])).

fof(f1720,plain,
    ( spl10_114
    | spl10_102
    | spl10_116
    | ~ spl10_100 ),
    inference(avatar_split_clause,[],[f1573,f1569,f1718,f1582,f1712])).

fof(f1573,plain,
    ( r2_hidden(sK5(sK5(k1_zfmisc_1(sK2))),u1_struct_0(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK5(k1_zfmisc_1(sK2)))
    | ~ spl10_100 ),
    inference(resolution,[],[f1570,f358])).

fof(f358,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK5(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(X0)
      | v1_xboole_0(sK5(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f341,f126])).

fof(f341,plain,(
    ! [X4] :
      ( m1_subset_1(sK5(sK5(k1_zfmisc_1(X4))),X4)
      | v1_xboole_0(sK5(k1_zfmisc_1(X4))) ) ),
    inference(resolution,[],[f338,f250])).

fof(f338,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X6,sK5(k1_zfmisc_1(X7)))
      | m1_subset_1(X6,X7) ) ),
    inference(resolution,[],[f133,f119])).

fof(f1625,plain,
    ( spl10_102
    | ~ spl10_113
    | ~ spl10_104 ),
    inference(avatar_split_clause,[],[f1610,f1588,f1623,f1582])).

fof(f1623,plain,
    ( spl10_113
  <=> ~ r1_xboole_0(u1_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_113])])).

fof(f1588,plain,
    ( spl10_104
  <=> r2_hidden(sK5(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f1610,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK0),sK2)
    | v1_xboole_0(sK2)
    | ~ spl10_104 ),
    inference(resolution,[],[f1592,f250])).

fof(f1592,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK2),X0)
        | ~ r1_xboole_0(u1_struct_0(sK0),X0) )
    | ~ spl10_104 ),
    inference(resolution,[],[f1589,f122])).

fof(f1589,plain,
    ( r2_hidden(sK5(sK2),u1_struct_0(sK0))
    | ~ spl10_104 ),
    inference(avatar_component_clause,[],[f1588])).

fof(f1618,plain,
    ( ~ spl10_111
    | ~ spl10_104 ),
    inference(avatar_split_clause,[],[f1611,f1588,f1616])).

fof(f1616,plain,
    ( spl10_111
  <=> ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_111])])).

fof(f1611,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl10_104 ),
    inference(resolution,[],[f1592,f1589])).

fof(f1609,plain,
    ( spl10_102
    | ~ spl10_109
    | ~ spl10_104 ),
    inference(avatar_split_clause,[],[f1591,f1588,f1607,f1582])).

fof(f1607,plain,
    ( spl10_109
  <=> ~ r1_xboole_0(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_109])])).

fof(f1591,plain,
    ( ~ r1_xboole_0(sK2,u1_struct_0(sK0))
    | v1_xboole_0(sK2)
    | ~ spl10_104 ),
    inference(resolution,[],[f1589,f257])).

fof(f1602,plain,
    ( ~ spl10_107
    | ~ spl10_104 ),
    inference(avatar_split_clause,[],[f1593,f1588,f1600])).

fof(f1600,plain,
    ( spl10_107
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_107])])).

fof(f1593,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK2))
    | ~ spl10_104 ),
    inference(resolution,[],[f1589,f124])).

fof(f1595,plain,
    ( ~ spl10_99
    | ~ spl10_104 ),
    inference(avatar_split_clause,[],[f1594,f1588,f1563])).

fof(f1563,plain,
    ( spl10_99
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f1594,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_104 ),
    inference(resolution,[],[f1589,f130])).

fof(f1590,plain,
    ( spl10_102
    | spl10_104
    | ~ spl10_100 ),
    inference(avatar_split_clause,[],[f1572,f1569,f1588,f1582])).

fof(f1572,plain,
    ( r2_hidden(sK5(sK2),u1_struct_0(sK0))
    | v1_xboole_0(sK2)
    | ~ spl10_100 ),
    inference(resolution,[],[f1570,f250])).

fof(f1571,plain,
    ( spl10_98
    | spl10_100
    | spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f1554,f228,f214,f172,f165,f158,f151,f144,f1569,f1566])).

fof(f1566,plain,
    ( spl10_98
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_98])])).

fof(f1554,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(resolution,[],[f1545,f126])).

fof(f1545,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_20
    | ~ spl10_24 ),
    inference(resolution,[],[f1501,f215])).

fof(f1501,plain,
    ( ! [X2,X3] :
        ( ~ m2_orders_2(X2,sK0,sK1)
        | m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,X2) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_24 ),
    inference(resolution,[],[f1490,f133])).

fof(f1490,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X0,sK0,sK1) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8
    | ~ spl10_24 ),
    inference(resolution,[],[f804,f229])).

fof(f804,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X0,sK0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f803,f145])).

fof(f803,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_struct_0(sK0) )
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f802,f152])).

fof(f802,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_4
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f801,f159])).

fof(f801,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_6
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f800,f173])).

fof(f800,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_6 ),
    inference(resolution,[],[f127,f166])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
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
    inference(flattening,[],[f68])).

fof(f68,plain,(
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
    inference(ennf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',dt_m2_orders_2)).

fof(f1442,plain,
    ( spl10_94
    | spl10_96
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f1429,f228,f1440,f1434])).

fof(f1434,plain,
    ( spl10_94
  <=> ! [X0] :
        ( m1_subset_1(X0,k2_zfmisc_1(k1_orders_1(u1_struct_0(sK0)),k3_tarski(k1_orders_1(u1_struct_0(sK0)))))
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f1440,plain,
    ( spl10_96
  <=> v1_xboole_0(k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f1429,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k2_zfmisc_1(k1_orders_1(u1_struct_0(sK0)),k3_tarski(k1_orders_1(u1_struct_0(sK0)))))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl10_24 ),
    inference(resolution,[],[f459,f229])).

fof(f459,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X0,X1)
      | v1_xboole_0(X1)
      | m1_subset_1(X2,k2_zfmisc_1(X1,k3_tarski(X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f113,f133])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k3_tarski(X0))))
      | ~ m1_orders_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k3_tarski(X0))))
          | ~ m1_orders_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_orders_1(X1,X0)
         => m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k3_tarski(X0)))) ) ) ),
    inference(pure_predicate_removal,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_orders_1(X1,X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k3_tarski(X0))))
            & v1_funct_1(X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_orders_1(X1,X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k3_tarski(X0))))
            & v1_funct_2(X1,X0,k3_tarski(X0))
            & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',dt_m1_orders_1)).

fof(f1286,plain,
    ( spl10_92
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | spl10_77 ),
    inference(avatar_split_clause,[],[f1275,f698,f282,f268,f193,f1284])).

fof(f1284,plain,
    ( spl10_92
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f698,plain,
    ( spl10_77
  <=> ~ r1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f1275,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_77 ),
    inference(resolution,[],[f799,f699])).

fof(f699,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_77 ),
    inference(avatar_component_clause,[],[f698])).

fof(f1243,plain,
    ( spl10_90
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | spl10_75 ),
    inference(avatar_split_clause,[],[f1190,f689,f282,f268,f193,f1241])).

fof(f1241,plain,
    ( spl10_90
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f689,plain,
    ( spl10_75
  <=> ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_75])])).

fof(f1190,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_75 ),
    inference(resolution,[],[f789,f690])).

fof(f690,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_75 ),
    inference(avatar_component_clause,[],[f689])).

fof(f1201,plain,
    ( spl10_88
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | spl10_39 ),
    inference(avatar_split_clause,[],[f1189,f332,f282,f268,f193,f1199])).

fof(f1199,plain,
    ( spl10_88
  <=> k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f332,plain,
    ( spl10_39
  <=> ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f1189,plain,
    ( k1_xboole_0 = sK6(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_14
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_39 ),
    inference(resolution,[],[f789,f333])).

fof(f333,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f332])).

fof(f1079,plain,
    ( spl10_86
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_84 ),
    inference(avatar_split_clause,[],[f1068,f1059,f282,f268,f1077])).

fof(f1077,plain,
    ( spl10_86
  <=> k1_xboole_0 = sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f1059,plain,
    ( spl10_84
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f1068,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_84 ),
    inference(forward_demodulation,[],[f1062,f283])).

fof(f1062,plain,
    ( sK5(k1_zfmisc_1(k1_xboole_0)) = sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_28
    | ~ spl10_84 ),
    inference(resolution,[],[f1060,f274])).

fof(f1060,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f1059])).

fof(f1061,plain,
    ( spl10_82
    | spl10_84
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f359,f193,f1059,f1053])).

fof(f1053,plain,
    ( spl10_82
  <=> ! [X1] : ~ r2_hidden(X1,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f359,plain,
    ( ! [X1] :
        ( v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
        | ~ r2_hidden(X1,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))) )
    | ~ spl10_14 ),
    inference(resolution,[],[f341,f258])).

fof(f863,plain,
    ( spl10_34
    | spl10_80
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f344,f282,f861,f313])).

fof(f313,plain,
    ( spl10_34
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f861,plain,
    ( spl10_80
  <=> ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X0)
        | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl10_30 ),
    inference(superposition,[],[f257,f283])).

fof(f708,plain,
    ( spl10_58
    | spl10_60
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f581,f487,f515,f509])).

fof(f515,plain,
    ( spl10_60
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_60])])).

fof(f487,plain,
    ( spl10_54
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f581,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_54 ),
    inference(resolution,[],[f488,f126])).

fof(f488,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f487])).

fof(f707,plain,
    ( ~ spl10_79
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f693,f509,f705])).

fof(f705,plain,
    ( spl10_79
  <=> ~ r1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f693,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_58 ),
    inference(resolution,[],[f680,f510])).

fof(f700,plain,
    ( ~ spl10_77
    | ~ spl10_36
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f692,f509,f319,f698])).

fof(f692,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_36
    | ~ spl10_58 ),
    inference(resolution,[],[f680,f320])).

fof(f691,plain,
    ( ~ spl10_75
    | ~ spl10_36
    | ~ spl10_58 ),
    inference(avatar_split_clause,[],[f684,f509,f319,f689])).

fof(f684,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_36
    | ~ spl10_58 ),
    inference(resolution,[],[f676,f510])).

fof(f673,plain,
    ( ~ spl10_35
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f325,f319,f310])).

fof(f310,plain,
    ( spl10_35
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f325,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_36 ),
    inference(resolution,[],[f320,f130])).

fof(f672,plain,
    ( spl10_72
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f661,f313,f282,f268,f670])).

fof(f670,plain,
    ( spl10_72
  <=> k1_zfmisc_1(k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f661,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_34 ),
    inference(forward_demodulation,[],[f655,f283])).

fof(f655,plain,
    ( k1_zfmisc_1(k1_xboole_0) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_28
    | ~ spl10_34 ),
    inference(resolution,[],[f314,f274])).

fof(f314,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f313])).

fof(f654,plain,
    ( spl10_34
    | ~ spl10_14
    | ~ spl10_70 ),
    inference(avatar_split_clause,[],[f648,f636,f193,f313])).

fof(f636,plain,
    ( spl10_70
  <=> k1_orders_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f648,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_14
    | ~ spl10_70 ),
    inference(subsumption_resolution,[],[f644,f194])).

fof(f644,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_70 ),
    inference(superposition,[],[f112,f637])).

fof(f637,plain,
    ( k1_orders_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f636])).

fof(f650,plain,
    ( ~ spl10_14
    | spl10_35
    | ~ spl10_70 ),
    inference(avatar_contradiction_clause,[],[f649])).

fof(f649,plain,
    ( $false
    | ~ spl10_14
    | ~ spl10_35
    | ~ spl10_70 ),
    inference(subsumption_resolution,[],[f648,f311])).

fof(f311,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f310])).

fof(f638,plain,
    ( spl10_70
    | ~ spl10_32
    | ~ spl10_66 ),
    inference(avatar_split_clause,[],[f617,f590,f299,f636])).

fof(f299,plain,
    ( spl10_32
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f590,plain,
    ( spl10_66
  <=> k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f617,plain,
    ( k1_orders_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | ~ spl10_32
    | ~ spl10_66 ),
    inference(forward_demodulation,[],[f604,f578])).

fof(f578,plain,
    ( ! [X10] : k1_xboole_0 = k7_subset_1(k1_xboole_0,k1_xboole_0,X10)
    | ~ spl10_32 ),
    inference(forward_demodulation,[],[f573,f108])).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',t4_boole)).

fof(f573,plain,
    ( ! [X10] : k7_subset_1(k1_xboole_0,k1_xboole_0,X10) = k4_xboole_0(k1_xboole_0,X10)
    | ~ spl10_32 ),
    inference(resolution,[],[f132,f300])).

fof(f300,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f299])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',redefinition_k7_subset_1)).

fof(f604,plain,
    ( k1_orders_1(k1_zfmisc_1(k1_xboole_0)) = k7_subset_1(k1_xboole_0,k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl10_66 ),
    inference(superposition,[],[f137,f591])).

fof(f591,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f590])).

fof(f630,plain,
    ( spl10_68
    | ~ spl10_66 ),
    inference(avatar_split_clause,[],[f600,f590,f628])).

fof(f628,plain,
    ( spl10_68
  <=> m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_68])])).

fof(f600,plain,
    ( m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl10_66 ),
    inference(superposition,[],[f139,f591])).

fof(f592,plain,
    ( spl10_66
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_60 ),
    inference(avatar_split_clause,[],[f556,f515,f282,f268,f590])).

fof(f556,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)) = k1_xboole_0
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_60 ),
    inference(forward_demodulation,[],[f550,f283])).

fof(f550,plain,
    ( k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_28
    | ~ spl10_60 ),
    inference(resolution,[],[f516,f274])).

fof(f516,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_60 ),
    inference(avatar_component_clause,[],[f515])).

fof(f585,plain,
    ( spl10_62
    | spl10_42
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f525,f465,f396,f537])).

fof(f537,plain,
    ( spl10_62
  <=> r2_hidden(k1_xboole_0,k1_orders_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f396,plain,
    ( spl10_42
  <=> v1_xboole_0(k1_orders_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f465,plain,
    ( spl10_50
  <=> m1_subset_1(k1_xboole_0,k1_orders_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f525,plain,
    ( v1_xboole_0(k1_orders_1(k1_xboole_0))
    | r2_hidden(k1_xboole_0,k1_orders_1(k1_xboole_0))
    | ~ spl10_50 ),
    inference(resolution,[],[f466,f126])).

fof(f466,plain,
    ( m1_subset_1(k1_xboole_0,k1_orders_1(k1_xboole_0))
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f465])).

fof(f567,plain,
    ( spl10_64
    | ~ spl10_44
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f541,f465,f415,f565])).

fof(f565,plain,
    ( spl10_64
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f415,plain,
    ( spl10_44
  <=> k1_orders_1(k1_xboole_0) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f541,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl10_44
    | ~ spl10_50 ),
    inference(superposition,[],[f466,f416])).

fof(f416,plain,
    ( k1_orders_1(k1_xboole_0) = k1_xboole_0
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f415])).

fof(f539,plain,
    ( spl10_62
    | spl10_43
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f458,f445,f393,f537])).

fof(f393,plain,
    ( spl10_43
  <=> ~ v1_xboole_0(k1_orders_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f445,plain,
    ( spl10_48
  <=> k1_xboole_0 = sK5(k1_orders_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f458,plain,
    ( r2_hidden(k1_xboole_0,k1_orders_1(k1_xboole_0))
    | ~ spl10_43
    | ~ spl10_48 ),
    inference(subsumption_resolution,[],[f455,f394])).

fof(f394,plain,
    ( ~ v1_xboole_0(k1_orders_1(k1_xboole_0))
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f393])).

fof(f455,plain,
    ( r2_hidden(k1_xboole_0,k1_orders_1(k1_xboole_0))
    | v1_xboole_0(k1_orders_1(k1_xboole_0))
    | ~ spl10_48 ),
    inference(superposition,[],[f250,f446])).

fof(f446,plain,
    ( k1_xboole_0 = sK5(k1_orders_1(k1_xboole_0))
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f445])).

fof(f517,plain,
    ( spl10_58
    | spl10_60
    | ~ spl10_54 ),
    inference(avatar_split_clause,[],[f491,f487,f515,f509])).

fof(f491,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_54 ),
    inference(resolution,[],[f488,f126])).

fof(f498,plain,
    ( ~ spl10_57
    | ~ spl10_44
    | spl10_49 ),
    inference(avatar_split_clause,[],[f482,f442,f415,f496])).

fof(f496,plain,
    ( spl10_57
  <=> k1_xboole_0 != sK5(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f442,plain,
    ( spl10_49
  <=> k1_xboole_0 != sK5(k1_orders_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f482,plain,
    ( k1_xboole_0 != sK5(k1_xboole_0)
    | ~ spl10_44
    | ~ spl10_49 ),
    inference(superposition,[],[f443,f416])).

fof(f443,plain,
    ( k1_xboole_0 != sK5(k1_orders_1(k1_xboole_0))
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f442])).

fof(f489,plain,
    ( spl10_54
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f471,f415,f487])).

fof(f471,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_44 ),
    inference(superposition,[],[f377,f416])).

fof(f481,plain,
    ( ~ spl10_53
    | ~ spl10_44
    | spl10_47 ),
    inference(avatar_split_clause,[],[f474,f422,f415,f479])).

fof(f479,plain,
    ( spl10_53
  <=> ~ v1_xboole_0(sK5(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f422,plain,
    ( spl10_47
  <=> ~ v1_xboole_0(sK5(k1_orders_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f474,plain,
    ( ~ v1_xboole_0(sK5(k1_xboole_0))
    | ~ spl10_44
    | ~ spl10_47 ),
    inference(superposition,[],[f423,f416])).

fof(f423,plain,
    ( ~ v1_xboole_0(sK5(k1_orders_1(k1_xboole_0)))
    | ~ spl10_47 ),
    inference(avatar_component_clause,[],[f422])).

fof(f467,plain,
    ( spl10_50
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f456,f445,f465])).

fof(f456,plain,
    ( m1_subset_1(k1_xboole_0,k1_orders_1(k1_xboole_0))
    | ~ spl10_48 ),
    inference(superposition,[],[f119,f446])).

fof(f447,plain,
    ( spl10_48
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f434,f425,f282,f268,f445])).

fof(f425,plain,
    ( spl10_46
  <=> v1_xboole_0(sK5(k1_orders_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f434,plain,
    ( k1_xboole_0 = sK5(k1_orders_1(k1_xboole_0))
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_46 ),
    inference(forward_demodulation,[],[f428,f283])).

fof(f428,plain,
    ( sK5(k1_orders_1(k1_xboole_0)) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_28
    | ~ spl10_46 ),
    inference(resolution,[],[f426,f274])).

fof(f426,plain,
    ( v1_xboole_0(sK5(k1_orders_1(k1_xboole_0)))
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f425])).

fof(f427,plain,
    ( spl10_46
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f418,f390,f425])).

fof(f390,plain,
    ( spl10_40
  <=> ! [X0] : ~ r2_hidden(X0,sK5(k1_orders_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f418,plain,
    ( v1_xboole_0(sK5(k1_orders_1(k1_xboole_0)))
    | ~ spl10_40 ),
    inference(resolution,[],[f391,f250])).

fof(f391,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(k1_orders_1(k1_xboole_0)))
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f390])).

fof(f417,plain,
    ( spl10_44
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f406,f396,f282,f268,f415])).

fof(f406,plain,
    ( k1_orders_1(k1_xboole_0) = k1_xboole_0
    | ~ spl10_28
    | ~ spl10_30
    | ~ spl10_42 ),
    inference(forward_demodulation,[],[f400,f283])).

fof(f400,plain,
    ( k1_orders_1(k1_xboole_0) = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_28
    | ~ spl10_42 ),
    inference(resolution,[],[f397,f274])).

fof(f397,plain,
    ( v1_xboole_0(k1_orders_1(k1_xboole_0))
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f396])).

fof(f398,plain,
    ( spl10_40
    | spl10_42
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f383,f193,f396,f390])).

fof(f383,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_orders_1(k1_xboole_0))
        | ~ r2_hidden(X0,sK5(k1_orders_1(k1_xboole_0))) )
    | ~ spl10_14 ),
    inference(resolution,[],[f380,f258])).

fof(f334,plain,
    ( ~ spl10_39
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f327,f319,f332])).

fof(f327,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_36 ),
    inference(resolution,[],[f323,f320])).

fof(f323,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k1_xboole_0,X1)
        | ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),X1) )
    | ~ spl10_36 ),
    inference(resolution,[],[f320,f122])).

fof(f326,plain,
    ( ~ spl10_35
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f325,f319,f310])).

fof(f321,plain,
    ( spl10_34
    | spl10_36
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f290,f282,f319,f313])).

fof(f290,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_30 ),
    inference(superposition,[],[f250,f283])).

fof(f301,plain,
    ( spl10_32
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f291,f282,f299])).

fof(f291,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_30 ),
    inference(superposition,[],[f119,f283])).

fof(f284,plain,
    ( spl10_30
    | ~ spl10_28 ),
    inference(avatar_split_clause,[],[f275,f268,f282])).

fof(f275,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_28 ),
    inference(resolution,[],[f269,f116])).

fof(f270,plain,
    ( spl10_28
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f263,f193,f268])).

fof(f263,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_14 ),
    inference(resolution,[],[f259,f250])).

fof(f259,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_14 ),
    inference(resolution,[],[f258,f119])).

fof(f239,plain,
    ( spl10_26
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f232,f200,f237])).

fof(f237,plain,
    ( spl10_26
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f232,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl10_16 ),
    inference(resolution,[],[f123,f201])).

fof(f230,plain,(
    spl10_24 ),
    inference(avatar_split_clause,[],[f101,f228])).

fof(f101,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,
    ( r1_xboole_0(sK2,sK3)
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f52,f82,f81,f80,f79])).

fof(f79,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( r1_xboole_0(X2,X3)
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r1_xboole_0(X2,X3)
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r1_xboole_0(X2,X3)
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( r1_xboole_0(X2,X3)
                & m2_orders_2(X3,X0,sK1) )
            & m2_orders_2(X2,X0,sK1) )
        & m1_orders_1(sK1,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( r1_xboole_0(X2,X3)
              & m2_orders_2(X3,X0,X1) )
          & m2_orders_2(X2,X0,X1) )
     => ( ? [X3] :
            ( r1_xboole_0(sK2,X3)
            & m2_orders_2(X3,X0,X1) )
        & m2_orders_2(sK2,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( r1_xboole_0(X2,X3)
          & m2_orders_2(X3,X0,X1) )
     => ( r1_xboole_0(X2,sK3)
        & m2_orders_2(sK3,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r1_xboole_0(X2,X3)
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( r1_xboole_0(X2,X3)
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',t82_orders_2)).

fof(f223,plain,(
    spl10_22 ),
    inference(avatar_split_clause,[],[f103,f221])).

fof(f103,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f83])).

fof(f216,plain,(
    spl10_20 ),
    inference(avatar_split_clause,[],[f102,f214])).

fof(f102,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f83])).

fof(f209,plain,(
    spl10_18 ),
    inference(avatar_split_clause,[],[f106,f207])).

fof(f207,plain,
    ( spl10_18
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f106,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',d2_xboole_0)).

fof(f202,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f104,f200])).

fof(f104,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f83])).

fof(f195,plain,(
    spl10_14 ),
    inference(avatar_split_clause,[],[f138,f193])).

fof(f138,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f105,f106])).

fof(f105,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',dt_o_0_0_xboole_0)).

fof(f188,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f136,f186])).

fof(f186,plain,
    ( spl10_12
  <=> l1_orders_2(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f136,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    l1_orders_2(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f23,f94])).

fof(f94,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK9) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',existence_l1_orders_2)).

fof(f181,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f135,f179])).

fof(f179,plain,
    ( spl10_10
  <=> l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f135,plain,(
    l1_struct_0(sK8) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    l1_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f24,f92])).

fof(f92,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK8) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t82_orders_2.p',existence_l1_struct_0)).

fof(f174,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f100,f172])).

fof(f100,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f167,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f99,f165])).

fof(f99,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f160,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f98,f158])).

fof(f98,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f153,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f97,f151])).

fof(f97,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f146,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f96,f144])).

fof(f96,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f83])).
%------------------------------------------------------------------------------
