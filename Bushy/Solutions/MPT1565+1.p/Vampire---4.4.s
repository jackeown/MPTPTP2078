%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t43_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:42 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  339 (1068 expanded)
%              Number of leaves         :   96 ( 465 expanded)
%              Depth                    :   12
%              Number of atoms          : 1124 (3695 expanded)
%              Number of equality atoms :    6 (  13 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f962,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f119,f126,f133,f140,f147,f156,f163,f176,f184,f193,f201,f209,f221,f230,f242,f252,f259,f266,f276,f283,f291,f310,f323,f330,f357,f368,f375,f426,f438,f445,f471,f480,f501,f515,f542,f551,f560,f571,f585,f600,f611,f629,f633,f635,f638,f666,f674,f709,f716,f749,f772,f808,f843,f862,f871,f883,f890,f897,f906,f921,f923,f944,f950,f961])).

fof(f961,plain,
    ( ~ spl10_6
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_108
    | ~ spl10_116
    | spl10_121 ),
    inference(avatar_contradiction_clause,[],[f960])).

fof(f960,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_108
    | ~ spl10_116
    | ~ spl10_121 ),
    inference(subsumption_resolution,[],[f956,f943])).

fof(f943,plain,
    ( ~ r1_orders_2(sK0,sK1(sK0),sK5(sK0,u1_struct_0(sK0),sK1(sK0)))
    | ~ spl10_121 ),
    inference(avatar_component_clause,[],[f942])).

fof(f942,plain,
    ( spl10_121
  <=> ~ r1_orders_2(sK0,sK1(sK0),sK5(sK0,u1_struct_0(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_121])])).

fof(f956,plain,
    ( r1_orders_2(sK0,sK1(sK0),sK5(sK0,u1_struct_0(sK0),sK1(sK0)))
    | ~ spl10_6
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_108
    | ~ spl10_116 ),
    inference(unit_resulting_resolution,[],[f132,f208,f200,f870,f905,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK2(X0,X1,X2),X2)
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',d9_lattice3)).

fof(f905,plain,
    ( r2_lattice3(sK0,u1_struct_0(sK0),sK5(sK0,u1_struct_0(sK0),sK1(sK0)))
    | ~ spl10_116 ),
    inference(avatar_component_clause,[],[f904])).

fof(f904,plain,
    ( spl10_116
  <=> r2_lattice3(sK0,u1_struct_0(sK0),sK5(sK0,u1_struct_0(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_116])])).

fof(f870,plain,
    ( m1_subset_1(sK5(sK0,u1_struct_0(sK0),sK1(sK0)),u1_struct_0(sK0))
    | ~ spl10_108 ),
    inference(avatar_component_clause,[],[f869])).

fof(f869,plain,
    ( spl10_108
  <=> m1_subset_1(sK5(sK0,u1_struct_0(sK0),sK1(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_108])])).

fof(f200,plain,
    ( m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl10_24
  <=> m1_subset_1(sK1(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f208,plain,
    ( r2_hidden(sK1(sK0),u1_struct_0(sK0))
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl10_26
  <=> r2_hidden(sK1(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f132,plain,
    ( l1_orders_2(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl10_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f950,plain,
    ( spl10_118
    | ~ spl10_6
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f872,f869,f131,f919])).

fof(f919,plain,
    ( spl10_118
  <=> r2_lattice3(sK0,k1_xboole_0,sK5(sK0,u1_struct_0(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_118])])).

fof(f872,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK5(sK0,u1_struct_0(sK0),sK1(sK0)))
    | ~ spl10_6
    | ~ spl10_108 ),
    inference(unit_resulting_resolution,[],[f132,f870,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',t6_yellow_0)).

fof(f944,plain,
    ( ~ spl10_121
    | ~ spl10_2
    | ~ spl10_6
    | spl10_19
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f700,f228,f199,f174,f131,f117,f942])).

fof(f117,plain,
    ( spl10_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f174,plain,
    ( spl10_19
  <=> ~ r1_yellow_0(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f228,plain,
    ( spl10_30
  <=> r2_lattice3(sK0,u1_struct_0(sK0),sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f700,plain,
    ( ~ r1_orders_2(sK0,sK1(sK0),sK5(sK0,u1_struct_0(sK0),sK1(sK0)))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f118,f132,f175,f229,f200,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK6(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK6(X0,X1))
              & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f59,f61,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK6(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',t15_yellow_0)).

fof(f229,plain,
    ( r2_lattice3(sK0,u1_struct_0(sK0),sK1(sK0))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f228])).

fof(f175,plain,
    ( ~ r1_yellow_0(sK0,u1_struct_0(sK0))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f174])).

fof(f118,plain,
    ( v5_orders_2(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f923,plain,
    ( ~ spl10_6
    | ~ spl10_108
    | spl10_119 ),
    inference(avatar_contradiction_clause,[],[f922])).

fof(f922,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_108
    | ~ spl10_119 ),
    inference(subsumption_resolution,[],[f917,f872])).

fof(f917,plain,
    ( ~ r2_lattice3(sK0,k1_xboole_0,sK5(sK0,u1_struct_0(sK0),sK1(sK0)))
    | ~ spl10_119 ),
    inference(avatar_component_clause,[],[f916])).

fof(f916,plain,
    ( spl10_119
  <=> ~ r2_lattice3(sK0,k1_xboole_0,sK5(sK0,u1_struct_0(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_119])])).

fof(f921,plain,
    ( spl10_118
    | ~ spl10_6
    | ~ spl10_54
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f874,f869,f355,f131,f919])).

fof(f355,plain,
    ( spl10_54
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_54])])).

fof(f874,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK5(sK0,u1_struct_0(sK0),sK1(sK0)))
    | ~ spl10_6
    | ~ spl10_54
    | ~ spl10_108 ),
    inference(unit_resulting_resolution,[],[f132,f378,f870,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f378,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl10_54 ),
    inference(unit_resulting_resolution,[],[f356,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',t7_boole)).

fof(f356,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_54 ),
    inference(avatar_component_clause,[],[f355])).

fof(f906,plain,
    ( spl10_116
    | ~ spl10_2
    | ~ spl10_6
    | spl10_19
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f681,f228,f199,f174,f131,f117,f904])).

fof(f681,plain,
    ( r2_lattice3(sK0,u1_struct_0(sK0),sK5(sK0,u1_struct_0(sK0),sK1(sK0)))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f118,f132,f175,f229,f200,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f897,plain,
    ( spl10_114
    | spl10_21
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f876,f869,f182,f895])).

fof(f895,plain,
    ( spl10_114
  <=> r2_hidden(sK5(sK0,u1_struct_0(sK0),sK1(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_114])])).

fof(f182,plain,
    ( spl10_21
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f876,plain,
    ( r2_hidden(sK5(sK0,u1_struct_0(sK0),sK1(sK0)),u1_struct_0(sK0))
    | ~ spl10_21
    | ~ spl10_108 ),
    inference(unit_resulting_resolution,[],[f183,f870,f101])).

fof(f101,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',t2_subset)).

fof(f183,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f890,plain,
    ( ~ spl10_113
    | spl10_21
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f875,f869,f182,f888])).

fof(f888,plain,
    ( spl10_113
  <=> ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,u1_struct_0(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_113])])).

fof(f875,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK5(sK0,u1_struct_0(sK0),sK1(sK0)))
    | ~ spl10_21
    | ~ spl10_108 ),
    inference(unit_resulting_resolution,[],[f183,f870,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f101,f99])).

fof(f99,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',antisymmetry_r2_hidden)).

fof(f883,plain,
    ( spl10_110
    | ~ spl10_6
    | ~ spl10_108 ),
    inference(avatar_split_clause,[],[f873,f869,f131,f881])).

fof(f881,plain,
    ( spl10_110
  <=> r1_lattice3(sK0,k1_xboole_0,sK5(sK0,u1_struct_0(sK0),sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_110])])).

fof(f873,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK5(sK0,u1_struct_0(sK0),sK1(sK0)))
    | ~ spl10_6
    | ~ spl10_108 ),
    inference(unit_resulting_resolution,[],[f132,f870,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,k1_xboole_0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f871,plain,
    ( spl10_108
    | ~ spl10_2
    | ~ spl10_6
    | spl10_19
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f652,f228,f199,f174,f131,f117,f869])).

fof(f652,plain,
    ( m1_subset_1(sK5(sK0,u1_struct_0(sK0),sK1(sK0)),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f118,f132,f175,f229,f200,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f862,plain,
    ( spl10_106
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_84
    | ~ spl10_86 ),
    inference(avatar_split_clause,[],[f819,f595,f583,f165,f131,f117,f860])).

fof(f860,plain,
    ( spl10_106
  <=> r1_orders_2(sK0,sK4(sK0,k1_xboole_0),sK4(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f165,plain,
    ( spl10_16
  <=> r2_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f583,plain,
    ( spl10_84
  <=> r1_lattice3(sK0,k1_xboole_0,sK4(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f595,plain,
    ( spl10_86
  <=> m1_subset_1(sK4(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f819,plain,
    ( r1_orders_2(sK0,sK4(sK0,k1_xboole_0),sK4(sK0,k1_xboole_0))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_84
    | ~ spl10_86 ),
    inference(unit_resulting_resolution,[],[f118,f132,f166,f584,f596,f88])).

fof(f88,plain,(
    ! [X0,X5,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X5,sK4(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK3(X0,X1,X2))
                  & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK4(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK4(X0,X1))
              & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK4(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK4(X0,X1))
        & m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',t16_yellow_0)).

fof(f596,plain,
    ( m1_subset_1(sK4(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_86 ),
    inference(avatar_component_clause,[],[f595])).

fof(f584,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK4(sK0,k1_xboole_0))
    | ~ spl10_84 ),
    inference(avatar_component_clause,[],[f583])).

fof(f166,plain,
    ( r2_yellow_0(sK0,k1_xboole_0)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f843,plain,
    ( spl10_104
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f809,f281,f165,f131,f117,f841])).

fof(f841,plain,
    ( spl10_104
  <=> r1_orders_2(sK0,sK7(u1_struct_0(sK0)),sK4(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f281,plain,
    ( spl10_42
  <=> r1_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f809,plain,
    ( r1_orders_2(sK0,sK7(u1_struct_0(sK0)),sK4(sK0,k1_xboole_0))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_42 ),
    inference(unit_resulting_resolution,[],[f118,f132,f282,f98,f166,f88])).

fof(f98,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f13,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',existence_m1_subset_1)).

fof(f282,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0)))
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f281])).

fof(f808,plain,
    ( ~ spl10_2
    | ~ spl10_6
    | spl10_17
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_40
    | ~ spl10_82
    | ~ spl10_98 ),
    inference(avatar_contradiction_clause,[],[f807])).

fof(f807,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_17
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_40
    | ~ spl10_82
    | ~ spl10_98 ),
    inference(subsumption_resolution,[],[f800,f750])).

fof(f750,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,k1_xboole_0,sK1(sK0)),sK1(sK0))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_17
    | ~ spl10_24
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f118,f132,f200,f275,f169,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f169,plain,
    ( ~ r2_yellow_0(sK0,k1_xboole_0)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl10_17
  <=> ~ r2_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f275,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK1(sK0))
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f274])).

fof(f274,plain,
    ( spl10_40
  <=> r1_lattice3(sK0,k1_xboole_0,sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f800,plain,
    ( r1_orders_2(sK0,sK3(sK0,k1_xboole_0,sK1(sK0)),sK1(sK0))
    | ~ spl10_6
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_82
    | ~ spl10_98 ),
    inference(unit_resulting_resolution,[],[f132,f200,f229,f570,f715,f81])).

fof(f715,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0,sK1(sK0)),u1_struct_0(sK0))
    | ~ spl10_98 ),
    inference(avatar_component_clause,[],[f714])).

fof(f714,plain,
    ( spl10_98
  <=> r2_hidden(sK3(sK0,k1_xboole_0,sK1(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_98])])).

fof(f570,plain,
    ( m1_subset_1(sK3(sK0,k1_xboole_0,sK1(sK0)),u1_struct_0(sK0))
    | ~ spl10_82 ),
    inference(avatar_component_clause,[],[f569])).

fof(f569,plain,
    ( spl10_82
  <=> m1_subset_1(sK3(sK0,k1_xboole_0,sK1(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f772,plain,
    ( spl10_102
    | ~ spl10_6
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_86
    | ~ spl10_88 ),
    inference(avatar_split_clause,[],[f730,f606,f595,f228,f199,f131,f770])).

fof(f770,plain,
    ( spl10_102
  <=> r1_orders_2(sK0,sK4(sK0,k1_xboole_0),sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_102])])).

fof(f606,plain,
    ( spl10_88
  <=> r2_hidden(sK4(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f730,plain,
    ( r1_orders_2(sK0,sK4(sK0,k1_xboole_0),sK1(sK0))
    | ~ spl10_6
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_86
    | ~ spl10_88 ),
    inference(unit_resulting_resolution,[],[f132,f200,f229,f596,f607,f81])).

fof(f607,plain,
    ( r2_hidden(sK4(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_88 ),
    inference(avatar_component_clause,[],[f606])).

fof(f749,plain,
    ( spl10_100
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f718,f274,f199,f165,f131,f117,f747])).

fof(f747,plain,
    ( spl10_100
  <=> r1_orders_2(sK0,sK1(sK0),sK4(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_100])])).

fof(f718,plain,
    ( r1_orders_2(sK0,sK1(sK0),sK4(sK0,k1_xboole_0))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f118,f132,f275,f200,f166,f88])).

fof(f716,plain,
    ( spl10_98
    | spl10_21
    | ~ spl10_82 ),
    inference(avatar_split_clause,[],[f696,f569,f182,f714])).

fof(f696,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0,sK1(sK0)),u1_struct_0(sK0))
    | ~ spl10_21
    | ~ spl10_82 ),
    inference(unit_resulting_resolution,[],[f183,f570,f101])).

fof(f709,plain,
    ( ~ spl10_97
    | spl10_21
    | ~ spl10_82 ),
    inference(avatar_split_clause,[],[f695,f569,f182,f707])).

fof(f707,plain,
    ( spl10_97
  <=> ~ r2_hidden(u1_struct_0(sK0),sK3(sK0,k1_xboole_0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_97])])).

fof(f695,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK3(sK0,k1_xboole_0,sK1(sK0)))
    | ~ spl10_21
    | ~ spl10_82 ),
    inference(unit_resulting_resolution,[],[f183,f570,f186])).

fof(f674,plain,
    ( spl10_94
    | ~ spl10_6
    | ~ spl10_54
    | ~ spl10_86 ),
    inference(avatar_split_clause,[],[f648,f595,f355,f131,f672])).

fof(f672,plain,
    ( spl10_94
  <=> r2_lattice3(sK0,k1_xboole_0,sK4(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f648,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK4(sK0,k1_xboole_0))
    | ~ spl10_6
    | ~ spl10_54
    | ~ spl10_86 ),
    inference(unit_resulting_resolution,[],[f132,f378,f596,f83])).

fof(f666,plain,
    ( ~ spl10_93
    | spl10_21
    | ~ spl10_86 ),
    inference(avatar_split_clause,[],[f650,f595,f182,f664])).

fof(f664,plain,
    ( spl10_93
  <=> ~ r2_hidden(u1_struct_0(sK0),sK4(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f650,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK4(sK0,k1_xboole_0))
    | ~ spl10_21
    | ~ spl10_86 ),
    inference(unit_resulting_resolution,[],[f183,f596,f186])).

fof(f638,plain,
    ( spl10_21
    | ~ spl10_86
    | spl10_89 ),
    inference(avatar_contradiction_clause,[],[f637])).

fof(f637,plain,
    ( $false
    | ~ spl10_21
    | ~ spl10_86
    | ~ spl10_89 ),
    inference(subsumption_resolution,[],[f596,f636])).

fof(f636,plain,
    ( ~ m1_subset_1(sK4(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_21
    | ~ spl10_89 ),
    inference(subsumption_resolution,[],[f613,f183])).

fof(f613,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_89 ),
    inference(resolution,[],[f610,f101])).

fof(f610,plain,
    ( ~ r2_hidden(sK4(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_89 ),
    inference(avatar_component_clause,[],[f609])).

fof(f609,plain,
    ( spl10_89
  <=> ~ r2_hidden(sK4(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_89])])).

fof(f635,plain,
    ( ~ spl10_2
    | ~ spl10_6
    | ~ spl10_16
    | spl10_87 ),
    inference(avatar_contradiction_clause,[],[f634])).

fof(f634,plain,
    ( $false
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_16
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f166,f631])).

fof(f631,plain,
    ( ~ r2_yellow_0(sK0,k1_xboole_0)
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f630,f118])).

fof(f630,plain,
    ( ~ r2_yellow_0(sK0,k1_xboole_0)
    | ~ v5_orders_2(sK0)
    | ~ spl10_6
    | ~ spl10_87 ),
    inference(subsumption_resolution,[],[f603,f132])).

fof(f603,plain,
    ( ~ r2_yellow_0(sK0,k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ spl10_87 ),
    inference(resolution,[],[f599,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f599,plain,
    ( ~ m1_subset_1(sK4(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_87 ),
    inference(avatar_component_clause,[],[f598])).

fof(f598,plain,
    ( spl10_87
  <=> ~ m1_subset_1(sK4(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_87])])).

fof(f633,plain,
    ( ~ spl10_6
    | ~ spl10_82
    | spl10_91 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | ~ spl10_6
    | ~ spl10_82
    | ~ spl10_91 ),
    inference(subsumption_resolution,[],[f625,f619])).

fof(f619,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK3(sK0,k1_xboole_0,sK1(sK0)))
    | ~ spl10_6
    | ~ spl10_82 ),
    inference(unit_resulting_resolution,[],[f132,f570,f80])).

fof(f625,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK3(sK0,k1_xboole_0,sK1(sK0)))
    | ~ spl10_91 ),
    inference(avatar_component_clause,[],[f624])).

fof(f624,plain,
    ( spl10_91
  <=> ~ r1_lattice3(sK0,k1_xboole_0,sK3(sK0,k1_xboole_0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_91])])).

fof(f629,plain,
    ( spl10_90
    | ~ spl10_2
    | ~ spl10_6
    | spl10_17
    | ~ spl10_24
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f589,f274,f199,f168,f131,f117,f627])).

fof(f627,plain,
    ( spl10_90
  <=> r1_lattice3(sK0,k1_xboole_0,sK3(sK0,k1_xboole_0,sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f589,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK3(sK0,k1_xboole_0,sK1(sK0)))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_17
    | ~ spl10_24
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f118,f132,f169,f275,f200,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f611,plain,
    ( ~ spl10_89
    | spl10_87 ),
    inference(avatar_split_clause,[],[f602,f598,f609])).

fof(f602,plain,
    ( ~ r2_hidden(sK4(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_87 ),
    inference(unit_resulting_resolution,[],[f599,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',t1_subset)).

fof(f600,plain,
    ( ~ spl10_87
    | ~ spl10_6
    | spl10_85 ),
    inference(avatar_split_clause,[],[f590,f580,f131,f598])).

fof(f580,plain,
    ( spl10_85
  <=> ~ r1_lattice3(sK0,k1_xboole_0,sK4(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_85])])).

fof(f590,plain,
    ( ~ m1_subset_1(sK4(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_6
    | ~ spl10_85 ),
    inference(unit_resulting_resolution,[],[f132,f581,f80])).

fof(f581,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK4(sK0,k1_xboole_0))
    | ~ spl10_85 ),
    inference(avatar_component_clause,[],[f580])).

fof(f585,plain,
    ( spl10_84
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f574,f165,f131,f117,f583])).

fof(f574,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK4(sK0,k1_xboole_0))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_16 ),
    inference(unit_resulting_resolution,[],[f118,f132,f166,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK4(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f571,plain,
    ( spl10_82
    | ~ spl10_2
    | ~ spl10_6
    | spl10_17
    | ~ spl10_24
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f562,f274,f199,f168,f131,f117,f569])).

fof(f562,plain,
    ( m1_subset_1(sK3(sK0,k1_xboole_0,sK1(sK0)),u1_struct_0(sK0))
    | ~ spl10_2
    | ~ spl10_6
    | ~ spl10_17
    | ~ spl10_24
    | ~ spl10_40 ),
    inference(unit_resulting_resolution,[],[f118,f132,f169,f275,f200,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f560,plain,
    ( ~ spl10_81
    | spl10_63 ),
    inference(avatar_split_clause,[],[f529,f421,f558])).

fof(f558,plain,
    ( spl10_81
  <=> ~ m1_subset_1(sK7(k1_xboole_0),sK7(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_81])])).

fof(f421,plain,
    ( spl10_63
  <=> ~ v1_xboole_0(sK7(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_63])])).

fof(f529,plain,
    ( ~ m1_subset_1(sK7(k1_xboole_0),sK7(k1_xboole_0))
    | ~ spl10_63 ),
    inference(unit_resulting_resolution,[],[f422,f526])).

fof(f526,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f525])).

fof(f525,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f295])).

fof(f295,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f186,f101])).

fof(f422,plain,
    ( ~ v1_xboole_0(sK7(k1_xboole_0))
    | ~ spl10_63 ),
    inference(avatar_component_clause,[],[f421])).

fof(f551,plain,
    ( ~ spl10_79
    | spl10_49 ),
    inference(avatar_split_clause,[],[f528,f305,f549])).

fof(f549,plain,
    ( spl10_79
  <=> ~ m1_subset_1(sK1(sK0),sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_79])])).

fof(f305,plain,
    ( spl10_49
  <=> ~ v1_xboole_0(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f528,plain,
    ( ~ m1_subset_1(sK1(sK0),sK1(sK0))
    | ~ spl10_49 ),
    inference(unit_resulting_resolution,[],[f306,f526])).

fof(f306,plain,
    ( ~ v1_xboole_0(sK1(sK0))
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f305])).

fof(f542,plain,
    ( ~ spl10_77
    | spl10_21 ),
    inference(avatar_split_clause,[],[f527,f182,f540])).

fof(f540,plain,
    ( spl10_77
  <=> ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_77])])).

fof(f527,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl10_21 ),
    inference(unit_resulting_resolution,[],[f183,f526])).

fof(f515,plain,
    ( spl10_74
    | ~ spl10_6
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f487,f228,f199,f191,f131,f513])).

fof(f513,plain,
    ( spl10_74
  <=> r1_orders_2(sK0,sK7(u1_struct_0(sK0)),sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f191,plain,
    ( spl10_22
  <=> r2_hidden(sK7(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f487,plain,
    ( r1_orders_2(sK0,sK7(u1_struct_0(sK0)),sK1(sK0))
    | ~ spl10_6
    | ~ spl10_22
    | ~ spl10_24
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f132,f200,f229,f192,f98,f81])).

fof(f192,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f191])).

fof(f501,plain,
    ( spl10_72
    | ~ spl10_6
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f488,f228,f207,f199,f131,f499])).

fof(f499,plain,
    ( spl10_72
  <=> r1_orders_2(sK0,sK1(sK0),sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f488,plain,
    ( r1_orders_2(sK0,sK1(sK0),sK1(sK0))
    | ~ spl10_6
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f132,f200,f229,f208,f200,f81])).

fof(f480,plain,
    ( spl10_70
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f451,f424,f478])).

fof(f478,plain,
    ( spl10_70
  <=> k1_xboole_0 = sK7(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f424,plain,
    ( spl10_62
  <=> v1_xboole_0(sK7(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f451,plain,
    ( k1_xboole_0 = sK7(k1_xboole_0)
    | ~ spl10_62 ),
    inference(unit_resulting_resolution,[],[f425,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',t6_boole)).

fof(f425,plain,
    ( v1_xboole_0(sK7(k1_xboole_0))
    | ~ spl10_62 ),
    inference(avatar_component_clause,[],[f424])).

fof(f471,plain,
    ( ~ spl10_69
    | spl10_61
    | ~ spl10_62 ),
    inference(avatar_split_clause,[],[f458,f424,f418,f469])).

fof(f469,plain,
    ( spl10_69
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f418,plain,
    ( spl10_61
  <=> ~ m1_subset_1(k1_xboole_0,sK7(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f458,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl10_61
    | ~ spl10_62 ),
    inference(backward_demodulation,[],[f451,f419])).

fof(f419,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK7(k1_xboole_0))
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f418])).

fof(f445,plain,
    ( spl10_66
    | spl10_63 ),
    inference(avatar_split_clause,[],[f428,f421,f443])).

fof(f443,plain,
    ( spl10_66
  <=> r2_hidden(sK7(sK7(k1_xboole_0)),sK7(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f428,plain,
    ( r2_hidden(sK7(sK7(k1_xboole_0)),sK7(k1_xboole_0))
    | ~ spl10_63 ),
    inference(unit_resulting_resolution,[],[f98,f422,f101])).

fof(f438,plain,
    ( ~ spl10_65
    | spl10_63 ),
    inference(avatar_split_clause,[],[f427,f421,f436])).

fof(f436,plain,
    ( spl10_65
  <=> ~ r2_hidden(sK7(k1_xboole_0),sK7(sK7(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_65])])).

fof(f427,plain,
    ( ~ r2_hidden(sK7(k1_xboole_0),sK7(sK7(k1_xboole_0)))
    | ~ spl10_63 ),
    inference(unit_resulting_resolution,[],[f98,f422,f186])).

fof(f426,plain,
    ( ~ spl10_61
    | spl10_62
    | spl10_57 ),
    inference(avatar_split_clause,[],[f385,f366,f424,f418])).

fof(f366,plain,
    ( spl10_57
  <=> ~ r2_hidden(k1_xboole_0,sK7(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f385,plain,
    ( v1_xboole_0(sK7(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,sK7(k1_xboole_0))
    | ~ spl10_57 ),
    inference(resolution,[],[f367,f101])).

fof(f367,plain,
    ( ~ r2_hidden(k1_xboole_0,sK7(k1_xboole_0))
    | ~ spl10_57 ),
    inference(avatar_component_clause,[],[f366])).

fof(f375,plain,
    ( spl10_58
    | spl10_55 ),
    inference(avatar_split_clause,[],[f359,f352,f373])).

fof(f373,plain,
    ( spl10_58
  <=> r2_hidden(sK7(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f352,plain,
    ( spl10_55
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f359,plain,
    ( r2_hidden(sK7(k1_xboole_0),k1_xboole_0)
    | ~ spl10_55 ),
    inference(unit_resulting_resolution,[],[f98,f353,f101])).

fof(f353,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_55 ),
    inference(avatar_component_clause,[],[f352])).

fof(f368,plain,
    ( ~ spl10_57
    | spl10_55 ),
    inference(avatar_split_clause,[],[f358,f352,f366])).

fof(f358,plain,
    ( ~ r2_hidden(k1_xboole_0,sK7(k1_xboole_0))
    | ~ spl10_55 ),
    inference(unit_resulting_resolution,[],[f98,f353,f186])).

fof(f357,plain,
    ( spl10_54
    | ~ spl10_48 ),
    inference(avatar_split_clause,[],[f345,f308,f355])).

fof(f308,plain,
    ( spl10_48
  <=> v1_xboole_0(sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f345,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_48 ),
    inference(backward_demodulation,[],[f334,f309])).

fof(f309,plain,
    ( v1_xboole_0(sK1(sK0))
    | ~ spl10_48 ),
    inference(avatar_component_clause,[],[f308])).

fof(f334,plain,
    ( k1_xboole_0 = sK1(sK0)
    | ~ spl10_48 ),
    inference(unit_resulting_resolution,[],[f309,f74])).

fof(f330,plain,
    ( spl10_52
    | spl10_49 ),
    inference(avatar_split_clause,[],[f313,f305,f328])).

fof(f328,plain,
    ( spl10_52
  <=> r2_hidden(sK7(sK1(sK0)),sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_52])])).

fof(f313,plain,
    ( r2_hidden(sK7(sK1(sK0)),sK1(sK0))
    | ~ spl10_49 ),
    inference(unit_resulting_resolution,[],[f98,f306,f101])).

fof(f323,plain,
    ( ~ spl10_51
    | spl10_49 ),
    inference(avatar_split_clause,[],[f312,f305,f321])).

fof(f321,plain,
    ( spl10_51
  <=> ~ r2_hidden(sK1(sK0),sK7(sK1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_51])])).

fof(f312,plain,
    ( ~ r2_hidden(sK1(sK0),sK7(sK1(sK0)))
    | ~ spl10_49 ),
    inference(unit_resulting_resolution,[],[f98,f306,f186])).

fof(f310,plain,
    ( ~ spl10_47
    | spl10_48
    | spl10_29 ),
    inference(avatar_split_clause,[],[f223,f219,f308,f302])).

fof(f302,plain,
    ( spl10_47
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f219,plain,
    ( spl10_29
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f223,plain,
    ( v1_xboole_0(sK1(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),sK1(sK0))
    | ~ spl10_29 ),
    inference(resolution,[],[f220,f101])).

fof(f220,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1(sK0))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f219])).

fof(f291,plain,
    ( spl10_44
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f268,f145,f289])).

fof(f289,plain,
    ( spl10_44
  <=> r1_lattice3(sK9,k1_xboole_0,sK7(u1_struct_0(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f145,plain,
    ( spl10_10
  <=> l1_orders_2(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f268,plain,
    ( r1_lattice3(sK9,k1_xboole_0,sK7(u1_struct_0(sK9)))
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f146,f98,f80])).

fof(f146,plain,
    ( l1_orders_2(sK9)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f283,plain,
    ( spl10_42
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f267,f131,f281])).

fof(f267,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0)))
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f132,f98,f80])).

fof(f276,plain,
    ( spl10_40
    | ~ spl10_6
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f269,f199,f131,f274])).

fof(f269,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK1(sK0))
    | ~ spl10_6
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f132,f200,f80])).

fof(f266,plain,
    ( spl10_38
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f244,f145,f264])).

fof(f264,plain,
    ( spl10_38
  <=> r2_lattice3(sK9,k1_xboole_0,sK7(u1_struct_0(sK9))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f244,plain,
    ( r2_lattice3(sK9,k1_xboole_0,sK7(u1_struct_0(sK9)))
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f146,f98,f79])).

fof(f259,plain,
    ( spl10_36
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f243,f131,f257])).

fof(f257,plain,
    ( spl10_36
  <=> r2_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f243,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK7(u1_struct_0(sK0)))
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f132,f98,f79])).

fof(f252,plain,
    ( spl10_34
    | ~ spl10_6
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f245,f199,f131,f250])).

fof(f250,plain,
    ( spl10_34
  <=> r2_lattice3(sK0,k1_xboole_0,sK1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f245,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK1(sK0))
    | ~ spl10_6
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f132,f200,f79])).

fof(f242,plain,
    ( ~ spl10_33
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f233,f191,f240])).

fof(f240,plain,
    ( spl10_33
  <=> ~ r2_hidden(u1_struct_0(sK0),sK7(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f233,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK7(u1_struct_0(sK0)))
    | ~ spl10_22 ),
    inference(unit_resulting_resolution,[],[f192,f99])).

fof(f230,plain,
    ( spl10_30
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f222,f131,f124,f228])).

fof(f124,plain,
    ( spl10_4
  <=> v2_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f222,plain,
    ( r2_lattice3(sK0,u1_struct_0(sK0),sK1(sK0))
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f132,f125,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_lattice3(X0,u1_struct_0(X0),sK1(X0))
      | ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r2_lattice3(X0,u1_struct_0(X0),sK1(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r2_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r2_lattice3(X0,u1_struct_0(X0),sK1(X0))
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r2_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( v2_yellow_0(X0)
          | ! [X1] :
              ( ~ r2_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r2_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v2_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',d5_yellow_0)).

fof(f125,plain,
    ( v2_yellow_0(sK0)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f221,plain,
    ( ~ spl10_29
    | ~ spl10_26 ),
    inference(avatar_split_clause,[],[f212,f207,f219])).

fof(f212,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1(sK0))
    | ~ spl10_26 ),
    inference(unit_resulting_resolution,[],[f208,f99])).

fof(f209,plain,
    ( spl10_26
    | spl10_21
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f202,f199,f182,f207])).

fof(f202,plain,
    ( r2_hidden(sK1(sK0),u1_struct_0(sK0))
    | ~ spl10_21
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f183,f200,f101])).

fof(f201,plain,
    ( spl10_24
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f194,f131,f124,f199])).

fof(f194,plain,
    ( m1_subset_1(sK1(sK0),u1_struct_0(sK0))
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f132,f125,f76])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),u1_struct_0(X0))
      | ~ v2_yellow_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f193,plain,
    ( spl10_22
    | spl10_21 ),
    inference(avatar_split_clause,[],[f185,f182,f191])).

fof(f185,plain,
    ( r2_hidden(sK7(u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_21 ),
    inference(unit_resulting_resolution,[],[f98,f183,f101])).

fof(f184,plain,
    ( ~ spl10_21
    | spl10_1
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f177,f154,f110,f182])).

fof(f110,plain,
    ( spl10_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f154,plain,
    ( spl10_12
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f177,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_1
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f111,f155,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',fc2_struct_0)).

fof(f155,plain,
    ( l1_struct_0(sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f111,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f176,plain,
    ( ~ spl10_17
    | ~ spl10_19 ),
    inference(avatar_split_clause,[],[f73,f174,f168])).

fof(f73,plain,
    ( ~ r1_yellow_0(sK0,u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ r1_yellow_0(sK0,u1_struct_0(sK0))
      | ~ r2_yellow_0(sK0,k1_xboole_0) )
    & l1_orders_2(sK0)
    & v2_yellow_0(sK0)
    & v5_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ( ~ r1_yellow_0(X0,u1_struct_0(X0))
          | ~ r2_yellow_0(X0,k1_xboole_0) )
        & l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ( ~ r1_yellow_0(sK0,u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,k1_xboole_0) )
      & l1_orders_2(sK0)
      & v2_yellow_0(sK0)
      & v5_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ( ~ r1_yellow_0(X0,u1_struct_0(X0))
        | ~ r2_yellow_0(X0,k1_xboole_0) )
      & l1_orders_2(X0)
      & v2_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ( ~ r1_yellow_0(X0,u1_struct_0(X0))
        | ~ r2_yellow_0(X0,k1_xboole_0) )
      & l1_orders_2(X0)
      & v2_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ( r1_yellow_0(X0,u1_struct_0(X0))
          & r2_yellow_0(X0,k1_xboole_0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r1_yellow_0(X0,u1_struct_0(X0))
        & r2_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',t43_yellow_0)).

fof(f163,plain,
    ( spl10_14
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f149,f145,f161])).

fof(f161,plain,
    ( spl10_14
  <=> l1_struct_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f149,plain,
    ( l1_struct_0(sK9)
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f146,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',dt_l1_orders_2)).

fof(f156,plain,
    ( spl10_12
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f148,f131,f154])).

fof(f148,plain,
    ( l1_struct_0(sK0)
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f132,f75])).

fof(f147,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f105,f145])).

fof(f105,plain,(
    l1_orders_2(sK9) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    l1_orders_2(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f11,f67])).

fof(f67,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK9) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',existence_l1_orders_2)).

fof(f140,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f104,f138])).

fof(f138,plain,
    ( spl10_8
  <=> l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f104,plain,(
    l1_struct_0(sK8) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    l1_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f12,f65])).

fof(f65,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK8) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t43_yellow_0.p',existence_l1_struct_0)).

fof(f133,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f72,f131])).

fof(f72,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f126,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f71,f124])).

fof(f71,plain,(
    v2_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f119,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f70,f117])).

fof(f70,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f112,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f69,f110])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
