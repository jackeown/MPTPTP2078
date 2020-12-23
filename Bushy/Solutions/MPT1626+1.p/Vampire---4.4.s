%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t6_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:01 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 194 expanded)
%              Number of leaves         :   17 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  527 (1232 expanded)
%              Number of equality atoms :   38 ( 132 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f96,f100,f104,f112,f116,f120,f124,f128,f132,f150,f167,f270,f300,f306])).

fof(f306,plain,
    ( spl8_1
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22
    | spl8_29
    | ~ spl8_50 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_29
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f166,f290])).

fof(f290,plain,
    ( r2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f289,f95])).

fof(f95,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl8_3
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f289,plain,
    ( v2_struct_0(sK0)
    | r2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f288,f115])).

fof(f115,plain,
    ( r2_yellow_0(sK0,sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_10
  <=> r2_yellow_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f288,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | r2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f287,f149])).

fof(f149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl8_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f287,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | r2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f286,f131])).

fof(f131,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_18
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f286,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | r2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f285,f123])).

fof(f123,plain,
    ( v4_yellow_0(sK1,sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl8_14
  <=> v4_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f285,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | r2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f284,f91])).

fof(f91,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_1
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f284,plain,
    ( v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | r2_yellow_0(sK1,sK2)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f283,f103])).

fof(f103,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl8_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f283,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | r2_yellow_0(sK1,sK2)
    | ~ spl8_4
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f276,f99])).

fof(f99,plain,
    ( v4_orders_2(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl8_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f276,plain,
    ( ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | r2_yellow_0(sK1,sK2)
    | ~ spl8_50 ),
    inference(resolution,[],[f269,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_yellow_0(X0,X2)
      | v2_struct_0(X0)
      | r2_yellow_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                & r2_yellow_0(X1,X2) )
              | ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
              | ~ r2_yellow_0(X0,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_yellow_0(X1,X0)
          | ~ v4_yellow_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                  & r2_yellow_0(X0,X2) )
               => ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                  & r2_yellow_0(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t6_waybel_0.p',t64_yellow_0)).

fof(f269,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl8_50
  <=> r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f166,plain,
    ( ~ r2_yellow_0(sK1,sK2)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl8_29
  <=> ~ r2_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f300,plain,
    ( spl8_1
    | spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22
    | spl8_27
    | ~ spl8_50 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_27
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f298,f163])).

fof(f163,plain,
    ( k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl8_27
  <=> k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f298,plain,
    ( k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f297,f95])).

fof(f297,plain,
    ( v2_struct_0(sK0)
    | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f296,f115])).

fof(f296,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_22
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f295,f149])).

fof(f295,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f294,f131])).

fof(f294,plain,
    ( ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f293,f123])).

fof(f293,plain,
    ( ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f292,f91])).

fof(f292,plain,
    ( v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f291,f103])).

fof(f291,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ spl8_4
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f277,f99])).

fof(f277,plain,
    ( ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ v4_yellow_0(sK1,sK0)
    | ~ m1_yellow_0(sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_yellow_0(sK0,sK2)
    | v2_struct_0(sK0)
    | k2_yellow_0(sK0,sK2) = k2_yellow_0(sK1,sK2)
    | ~ spl8_50 ),
    inference(resolution,[],[f269,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_yellow_0(X0,X2)
      | v2_struct_0(X0)
      | k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f270,plain,
    ( spl8_50
    | spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | spl8_13
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f249,f148,f130,f126,f118,f114,f110,f102,f94,f268])).

fof(f110,plain,
    ( spl8_8
  <=> v2_waybel_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f118,plain,
    ( spl8_13
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f126,plain,
    ( spl8_16
  <=> v3_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f249,plain,
    ( r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_13
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f248,f119])).

fof(f119,plain,
    ( k1_xboole_0 != sK2
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f248,plain,
    ( k1_xboole_0 = sK2
    | r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_10
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f247,f115])).

fof(f247,plain,
    ( ~ r2_yellow_0(sK0,sK2)
    | k1_xboole_0 = sK2
    | r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f245,f111])).

fof(f111,plain,
    ( v2_waybel_0(sK2,sK1)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f245,plain,
    ( ~ v2_waybel_0(sK2,sK1)
    | ~ r2_yellow_0(sK0,sK2)
    | k1_xboole_0 = sK2
    | r2_hidden(k2_yellow_0(sK0,sK2),u1_struct_0(sK1))
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_16
    | ~ spl8_18
    | ~ spl8_22 ),
    inference(resolution,[],[f142,f149])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v2_waybel_0(X0,sK1)
        | ~ r2_yellow_0(sK0,X0)
        | k1_xboole_0 = X0
        | r2_hidden(k2_yellow_0(sK0,X0),u1_struct_0(sK1)) )
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f141,f127])).

fof(f127,plain,
    ( v3_waybel_0(sK1,sK0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ v2_waybel_0(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_yellow_0(sK0,X0)
        | k1_xboole_0 = X0
        | r2_hidden(k2_yellow_0(sK0,X0),u1_struct_0(sK1))
        | ~ v3_waybel_0(sK1,sK0) )
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f140,f95])).

fof(f140,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_waybel_0(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_yellow_0(sK0,X0)
        | k1_xboole_0 = X0
        | r2_hidden(k2_yellow_0(sK0,X0),u1_struct_0(sK1))
        | ~ v3_waybel_0(sK1,sK0) )
    | ~ spl8_6
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f134,f103])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ v2_waybel_0(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ r2_yellow_0(sK0,X0)
        | k1_xboole_0 = X0
        | r2_hidden(k2_yellow_0(sK0,X0),u1_struct_0(sK1))
        | ~ v3_waybel_0(sK1,sK0) )
    | ~ spl8_18 ),
    inference(resolution,[],[f131,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v2_waybel_0(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_yellow_0(X0,X2)
      | k1_xboole_0 = X2
      | r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
      | ~ v3_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r2_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_waybel_0(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                | k1_xboole_0 = X2
                | ~ r2_yellow_0(X0,X2)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                | ~ v2_waybel_0(X2,X1) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v3_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_0(X2,X1) )
               => ( r2_yellow_0(X0,X2)
                 => ( r2_hidden(k2_yellow_0(X0,X2),u1_struct_0(X1))
                    | k1_xboole_0 = X2 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t6_waybel_0.p',d3_waybel_0)).

fof(f167,plain,
    ( ~ spl8_27
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f53,f165,f162])).

fof(f53,plain,
    ( ~ r2_yellow_0(sK1,sK2)
    | k2_yellow_0(sK0,sK2) != k2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r2_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v2_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v3_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_yellow_0(X0,X2) != k2_yellow_0(X1,X2)
                | ~ r2_yellow_0(X1,X2) )
              & k1_xboole_0 != X2
              & r2_yellow_0(X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
              & v2_waybel_0(X2,X1) )
          & m1_yellow_0(X1,X0)
          & v3_waybel_0(X1,X0)
          & v4_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v3_waybel_0(X1,X0)
              & v4_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                  & v2_waybel_0(X2,X1) )
               => ( r2_yellow_0(X0,X2)
                 => ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                      & r2_yellow_0(X1,X2) )
                    | k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v3_waybel_0(X1,X0)
            & v4_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                & v2_waybel_0(X2,X1) )
             => ( r2_yellow_0(X0,X2)
               => ( ( k2_yellow_0(X0,X2) = k2_yellow_0(X1,X2)
                    & r2_yellow_0(X1,X2) )
                  | k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t6_waybel_0.p',t6_waybel_0)).

fof(f150,plain,(
    spl8_22 ),
    inference(avatar_split_clause,[],[f55,f148])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f132,plain,(
    spl8_18 ),
    inference(avatar_split_clause,[],[f61,f130])).

fof(f61,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f128,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f60,f126])).

fof(f60,plain,(
    v3_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f124,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f59,f122])).

fof(f59,plain,(
    v4_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f120,plain,(
    ~ spl8_13 ),
    inference(avatar_split_clause,[],[f57,f118])).

fof(f57,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f116,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f56,f114])).

fof(f56,plain,(
    r2_yellow_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f112,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f54,f110])).

fof(f54,plain,(
    v2_waybel_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f104,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f64,f102])).

fof(f64,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f100,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f63,f98])).

fof(f63,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f62,f94])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f92,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f58,f90])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
