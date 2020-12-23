%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t59_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:45 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 397 expanded)
%              Number of leaves         :   56 ( 180 expanded)
%              Depth                    :    7
%              Number of atoms          :  455 (1085 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f401,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f101,f108,f115,f122,f129,f136,f143,f152,f159,f168,f175,f186,f195,f202,f213,f220,f230,f237,f244,f251,f258,f266,f275,f290,f303,f311,f318,f326,f335,f345,f359,f374,f384,f397,f400])).

fof(f400,plain,
    ( spl7_15
    | ~ spl7_48
    | ~ spl7_68 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl7_15
    | ~ spl7_48
    | ~ spl7_68 ),
    inference(subsumption_resolution,[],[f398,f336])).

fof(f336,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_15
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f289,f142,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',t4_subset)).

fof(f142,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl7_15
  <=> ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f289,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl7_48
  <=> r2_hidden(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f398,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_68 ),
    inference(unit_resulting_resolution,[],[f396,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',t3_subset)).

fof(f396,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl7_68
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f397,plain,
    ( spl7_68
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f385,f184,f127,f99,f395])).

fof(f99,plain,
    ( spl7_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f127,plain,
    ( spl7_10
  <=> m1_yellow_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f184,plain,
    ( spl7_24
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f385,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl7_2
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f100,f185,f128,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_yellow_0(X1,X0)
              | ~ r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
            & ( ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
                & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) )
              | ~ m1_yellow_0(X1,X0) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) )
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( m1_yellow_0(X1,X0)
          <=> ( r1_tarski(u1_orders_2(X1),u1_orders_2(X0))
              & r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',d13_yellow_0)).

fof(f128,plain,
    ( m1_yellow_0(sK1,sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f127])).

fof(f185,plain,
    ( l1_orders_2(sK1)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f184])).

fof(f100,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f384,plain,
    ( spl7_66
    | ~ spl7_64 ),
    inference(avatar_split_clause,[],[f377,f372,f382])).

fof(f382,plain,
    ( spl7_66
  <=> l1_struct_0(sK3(sK3(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f372,plain,
    ( spl7_64
  <=> l1_orders_2(sK3(sK3(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f377,plain,
    ( l1_struct_0(sK3(sK3(sK6)))
    | ~ spl7_64 ),
    inference(unit_resulting_resolution,[],[f373,f68])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',dt_l1_orders_2)).

fof(f373,plain,
    ( l1_orders_2(sK3(sK3(sK6)))
    | ~ spl7_64 ),
    inference(avatar_component_clause,[],[f372])).

fof(f374,plain,
    ( spl7_64
    | ~ spl7_32
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f367,f357,f218,f372])).

fof(f218,plain,
    ( spl7_32
  <=> l1_orders_2(sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f357,plain,
    ( spl7_62
  <=> m1_yellow_0(sK3(sK3(sK6)),sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f367,plain,
    ( l1_orders_2(sK3(sK3(sK6)))
    | ~ spl7_32
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f219,f358,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',dt_m1_yellow_0)).

fof(f358,plain,
    ( m1_yellow_0(sK3(sK3(sK6)),sK3(sK6))
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f357])).

fof(f219,plain,
    ( l1_orders_2(sK3(sK6))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f218])).

fof(f359,plain,
    ( spl7_62
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f221,f218,f357])).

fof(f221,plain,
    ( m1_yellow_0(sK3(sK3(sK6)),sK3(sK6))
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f219,f74])).

fof(f74,plain,(
    ! [X0] :
      ( m1_yellow_0(sK3(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( m1_yellow_0(sK3(X0),X0)
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : m1_yellow_0(X1,X0)
     => m1_yellow_0(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ? [X1] : m1_yellow_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',existence_m1_yellow_0)).

fof(f345,plain,
    ( ~ spl7_61
    | spl7_15 ),
    inference(avatar_split_clause,[],[f337,f141,f343])).

fof(f343,plain,
    ( spl7_61
  <=> ~ r2_hidden(sK2,sK4(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f337,plain,
    ( ~ r2_hidden(sK2,sK4(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f142,f76,f84])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',existence_m1_subset_1)).

fof(f335,plain,
    ( spl7_58
    | ~ spl7_56 ),
    inference(avatar_split_clause,[],[f328,f324,f333])).

fof(f333,plain,
    ( spl7_58
  <=> l1_struct_0(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f324,plain,
    ( spl7_56
  <=> l1_orders_2(sK3(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f328,plain,
    ( l1_struct_0(sK3(sK3(sK0)))
    | ~ spl7_56 ),
    inference(unit_resulting_resolution,[],[f325,f68])).

fof(f325,plain,
    ( l1_orders_2(sK3(sK3(sK0)))
    | ~ spl7_56 ),
    inference(avatar_component_clause,[],[f324])).

fof(f326,plain,
    ( spl7_56
    | ~ spl7_28
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f319,f309,f200,f324])).

fof(f200,plain,
    ( spl7_28
  <=> l1_orders_2(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f309,plain,
    ( spl7_52
  <=> m1_yellow_0(sK3(sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f319,plain,
    ( l1_orders_2(sK3(sK3(sK0)))
    | ~ spl7_28
    | ~ spl7_52 ),
    inference(unit_resulting_resolution,[],[f201,f310,f73])).

fof(f310,plain,
    ( m1_yellow_0(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f309])).

fof(f201,plain,
    ( l1_orders_2(sK3(sK0))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f200])).

fof(f318,plain,
    ( spl7_54
    | spl7_31 ),
    inference(avatar_split_clause,[],[f277,f211,f316])).

fof(f316,plain,
    ( spl7_54
  <=> r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f211,plain,
    ( spl7_31
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f277,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f76,f212,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',t2_subset)).

fof(f212,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f211])).

fof(f311,plain,
    ( spl7_52
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f205,f200,f309])).

fof(f205,plain,
    ( m1_yellow_0(sK3(sK3(sK0)),sK3(sK0))
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f201,f74])).

fof(f303,plain,
    ( ~ spl7_51
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f293,f288,f301])).

fof(f301,plain,
    ( spl7_51
  <=> ~ r2_hidden(u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f293,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK2)
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f289,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',antisymmetry_r2_hidden)).

fof(f290,plain,
    ( spl7_48
    | ~ spl7_12
    | spl7_35 ),
    inference(avatar_split_clause,[],[f278,f228,f134,f288])).

fof(f134,plain,
    ( spl7_12
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f228,plain,
    ( spl7_35
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f278,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | ~ spl7_12
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f135,f229,f79])).

fof(f229,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f228])).

fof(f135,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f275,plain,
    ( spl7_46
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f268,f264,f273])).

fof(f273,plain,
    ( spl7_46
  <=> l1_struct_0(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f264,plain,
    ( spl7_44
  <=> l1_orders_2(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f268,plain,
    ( l1_struct_0(sK3(sK1))
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f265,f68])).

fof(f265,plain,
    ( l1_orders_2(sK3(sK1))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f264])).

fof(f266,plain,
    ( spl7_44
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f259,f256,f184,f264])).

fof(f256,plain,
    ( spl7_42
  <=> m1_yellow_0(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f259,plain,
    ( l1_orders_2(sK3(sK1))
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f185,f257,f73])).

fof(f257,plain,
    ( m1_yellow_0(sK3(sK1),sK1)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f256])).

fof(f258,plain,
    ( spl7_42
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f187,f184,f256])).

fof(f187,plain,
    ( m1_yellow_0(sK3(sK1),sK1)
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f185,f74])).

fof(f251,plain,
    ( ~ spl7_41
    | spl7_15 ),
    inference(avatar_split_clause,[],[f176,f141,f249])).

fof(f249,plain,
    ( spl7_41
  <=> ~ r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f176,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f142,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',t1_subset)).

fof(f244,plain,
    ( spl7_38
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f222,f218,f242])).

fof(f242,plain,
    ( spl7_38
  <=> l1_struct_0(sK3(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f222,plain,
    ( l1_struct_0(sK3(sK6))
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f219,f68])).

fof(f237,plain,
    ( spl7_36
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f206,f200,f235])).

fof(f235,plain,
    ( spl7_36
  <=> l1_struct_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f206,plain,
    ( l1_struct_0(sK3(sK0))
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f201,f68])).

fof(f230,plain,
    ( ~ spl7_35
    | spl7_5
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f204,f193,f106,f228])).

fof(f106,plain,
    ( spl7_5
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f193,plain,
    ( spl7_26
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f204,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_5
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f107,f194,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',fc2_struct_0)).

fof(f194,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f193])).

fof(f107,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f220,plain,
    ( spl7_32
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f179,f173,f120,f218])).

fof(f120,plain,
    ( spl7_8
  <=> l1_orders_2(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f173,plain,
    ( spl7_22
  <=> m1_yellow_0(sK3(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f179,plain,
    ( l1_orders_2(sK3(sK6))
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f121,f174,f73])).

fof(f174,plain,
    ( m1_yellow_0(sK3(sK6),sK6)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f173])).

fof(f121,plain,
    ( l1_orders_2(sK6)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f213,plain,
    ( ~ spl7_31
    | spl7_1
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f203,f150,f92,f211])).

fof(f92,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f150,plain,
    ( spl7_16
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f203,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_1
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f93,f151,f75])).

fof(f151,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f93,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f202,plain,
    ( spl7_28
    | ~ spl7_2
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f178,f166,f99,f200])).

fof(f166,plain,
    ( spl7_20
  <=> m1_yellow_0(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f178,plain,
    ( l1_orders_2(sK3(sK0))
    | ~ spl7_2
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f100,f167,f73])).

fof(f167,plain,
    ( m1_yellow_0(sK3(sK0),sK0)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f166])).

fof(f195,plain,
    ( spl7_26
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f188,f184,f193])).

fof(f188,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f185,f68])).

fof(f186,plain,
    ( spl7_24
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f177,f127,f99,f184])).

fof(f177,plain,
    ( l1_orders_2(sK1)
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f100,f128,f73])).

fof(f175,plain,
    ( spl7_22
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f161,f120,f173])).

fof(f161,plain,
    ( m1_yellow_0(sK3(sK6),sK6)
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f121,f74])).

fof(f168,plain,
    ( spl7_20
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f160,f99,f166])).

fof(f160,plain,
    ( m1_yellow_0(sK3(sK0),sK0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f100,f74])).

fof(f159,plain,
    ( spl7_18
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f145,f120,f157])).

fof(f157,plain,
    ( spl7_18
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f145,plain,
    ( l1_struct_0(sK6)
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f121,f68])).

fof(f152,plain,
    ( spl7_16
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f144,f99,f150])).

fof(f144,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f100,f68])).

fof(f143,plain,(
    ~ spl7_15 ),
    inference(avatar_split_clause,[],[f66,f141])).

fof(f66,plain,(
    ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & m1_yellow_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,u1_struct_0(X0))
                & m1_subset_1(X2,u1_struct_0(X1)) )
            & m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(sK0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ m1_subset_1(X2,u1_struct_0(X0))
            & m1_subset_1(X2,u1_struct_0(sK1)) )
        & m1_yellow_0(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(X2,u1_struct_0(X0))
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ m1_subset_1(sK2,u1_struct_0(X0))
        & m1_subset_1(sK2,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,u1_struct_0(X0))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & m1_yellow_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',t59_yellow_0)).

fof(f136,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f65,f134])).

fof(f65,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f129,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f64,f127])).

fof(f64,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f122,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f87,f120])).

fof(f87,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    l1_orders_2(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f59])).

fof(f59,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK6) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',existence_l1_orders_2)).

fof(f115,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f86,f113])).

fof(f113,plain,
    ( spl7_6
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f86,plain,(
    l1_struct_0(sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    l1_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f15,f57])).

fof(f57,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK5) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t59_yellow_0.p',existence_l1_struct_0)).

fof(f108,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f63,f106])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f101,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f62,f99])).

fof(f62,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f61,f92])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
