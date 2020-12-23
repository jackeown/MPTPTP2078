%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t9_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:48 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  414 (1425 expanded)
%              Number of leaves         :  109 ( 594 expanded)
%              Depth                    :   10
%              Number of atoms          : 1192 (4507 expanded)
%              Number of equality atoms :    7 (  74 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1082,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f97,f104,f111,f119,f132,f139,f146,f147,f168,f179,f197,f205,f220,f227,f242,f249,f256,f269,f279,f286,f293,f300,f327,f338,f345,f389,f406,f414,f424,f426,f460,f473,f474,f490,f505,f515,f526,f538,f545,f552,f561,f571,f587,f588,f590,f592,f594,f596,f642,f677,f684,f699,f716,f723,f730,f737,f754,f761,f773,f780,f787,f794,f801,f808,f815,f822,f835,f845,f852,f859,f866,f873,f890,f892,f916,f930,f937,f944,f951,f968,f973,f982,f989,f996,f1018,f1030,f1038,f1046,f1054,f1061,f1068,f1075,f1081])).

fof(f1081,plain,
    ( ~ spl8_0
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_138
    | spl8_155
    | ~ spl8_156 ),
    inference(avatar_contradiction_clause,[],[f1080])).

fof(f1080,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_138
    | ~ spl8_155
    | ~ spl8_156 ),
    inference(subsumption_resolution,[],[f1079,f1074])).

fof(f1074,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl8_156 ),
    inference(avatar_component_clause,[],[f1073])).

fof(f1073,plain,
    ( spl8_156
  <=> m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_156])])).

fof(f1079,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_138
    | ~ spl8_155 ),
    inference(unit_resulting_resolution,[],[f89,f110,f131,f988,f1067,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f29])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',d9_lattice3)).

fof(f1067,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3)
    | ~ spl8_155 ),
    inference(avatar_component_clause,[],[f1066])).

fof(f1066,plain,
    ( spl8_155
  <=> ~ r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_155])])).

fof(f988,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK2)
    | ~ spl8_138 ),
    inference(avatar_component_clause,[],[f987])).

fof(f987,plain,
    ( spl8_138
  <=> r2_hidden(sK4(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).

fof(f131,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_12
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f110,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f89,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl8_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f1075,plain,
    ( spl8_156
    | ~ spl8_0
    | ~ spl8_6
    | spl8_17 ),
    inference(avatar_split_clause,[],[f898,f144,f109,f88,f1073])).

fof(f144,plain,
    ( spl8_17
  <=> ~ r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f898,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f89,f110,f145,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f145,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f1068,plain,
    ( ~ spl8_155
    | ~ spl8_0
    | ~ spl8_6
    | spl8_17 ),
    inference(avatar_split_clause,[],[f897,f144,f109,f88,f1066])).

fof(f897,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK3),sK3)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f89,f110,f145,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1061,plain,
    ( spl8_152
    | ~ spl8_0
    | ~ spl8_6
    | spl8_11 ),
    inference(avatar_split_clause,[],[f894,f121,f109,f88,f1059])).

fof(f1059,plain,
    ( spl8_152
  <=> m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_152])])).

fof(f121,plain,
    ( spl8_11
  <=> ~ r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f894,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f89,f110,f122,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',d8_lattice3)).

fof(f122,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f1054,plain,
    ( ~ spl8_151
    | ~ spl8_0
    | ~ spl8_6
    | spl8_11 ),
    inference(avatar_split_clause,[],[f893,f121,f109,f88,f1052])).

fof(f1052,plain,
    ( spl8_151
  <=> ~ r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_151])])).

fof(f893,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f89,f110,f122,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1046,plain,
    ( ~ spl8_149
    | spl8_143 ),
    inference(avatar_split_clause,[],[f1020,f1016,f1044])).

fof(f1044,plain,
    ( spl8_149
  <=> ~ r2_hidden(sK2,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).

fof(f1016,plain,
    ( spl8_143
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_143])])).

fof(f1020,plain,
    ( ~ r2_hidden(sK2,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl8_143 ),
    inference(unit_resulting_resolution,[],[f74,f1017,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',t4_subset)).

fof(f1017,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_143 ),
    inference(avatar_component_clause,[],[f1016])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',existence_m1_subset_1)).

fof(f1038,plain,
    ( ~ spl8_147
    | spl8_143 ),
    inference(avatar_split_clause,[],[f1021,f1016,f1036])).

fof(f1036,plain,
    ( spl8_147
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).

fof(f1021,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_143 ),
    inference(unit_resulting_resolution,[],[f1017,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',t1_subset)).

fof(f1030,plain,
    ( ~ spl8_145
    | spl8_143 ),
    inference(avatar_split_clause,[],[f1019,f1016,f1028])).

fof(f1028,plain,
    ( spl8_145
  <=> ~ r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_145])])).

fof(f1019,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl8_143 ),
    inference(unit_resulting_resolution,[],[f1017,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',t3_subset)).

fof(f1018,plain,
    ( ~ spl8_143
    | ~ spl8_122
    | spl8_141 ),
    inference(avatar_split_clause,[],[f1009,f994,f871,f1016])).

fof(f871,plain,
    ( spl8_122
  <=> r2_hidden(sK5(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).

fof(f994,plain,
    ( spl8_141
  <=> ~ m1_subset_1(sK5(sK0,sK1,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).

fof(f1009,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_122
    | ~ spl8_141 ),
    inference(unit_resulting_resolution,[],[f872,f995,f81])).

fof(f995,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),k1_xboole_0)
    | ~ spl8_141 ),
    inference(avatar_component_clause,[],[f994])).

fof(f872,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK2)
    | ~ spl8_122 ),
    inference(avatar_component_clause,[],[f871])).

fof(f996,plain,
    ( ~ spl8_141
    | spl8_53
    | spl8_135 ),
    inference(avatar_split_clause,[],[f969,f966,f384,f994])).

fof(f384,plain,
    ( spl8_53
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f966,plain,
    ( spl8_135
  <=> ~ r2_hidden(sK5(sK0,sK1,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_135])])).

fof(f969,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),k1_xboole_0)
    | ~ spl8_53
    | ~ spl8_135 ),
    inference(unit_resulting_resolution,[],[f385,f967,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',t2_subset)).

fof(f967,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK3),k1_xboole_0)
    | ~ spl8_135 ),
    inference(avatar_component_clause,[],[f966])).

fof(f385,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f384])).

fof(f989,plain,
    ( spl8_138
    | spl8_25
    | ~ spl8_128 ),
    inference(avatar_split_clause,[],[f958,f935,f203,f987])).

fof(f203,plain,
    ( spl8_25
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f935,plain,
    ( spl8_128
  <=> m1_subset_1(sK4(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_128])])).

fof(f958,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK2)
    | ~ spl8_25
    | ~ spl8_128 ),
    inference(unit_resulting_resolution,[],[f204,f936,f77])).

fof(f936,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK2)
    | ~ spl8_128 ),
    inference(avatar_component_clause,[],[f935])).

fof(f204,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f203])).

fof(f982,plain,
    ( ~ spl8_137
    | spl8_25
    | ~ spl8_128 ),
    inference(avatar_split_clause,[],[f957,f935,f203,f980])).

fof(f980,plain,
    ( spl8_137
  <=> ~ r2_hidden(sK2,sK4(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).

fof(f957,plain,
    ( ~ r2_hidden(sK2,sK4(sK0,sK1,sK3))
    | ~ spl8_25
    | ~ spl8_128 ),
    inference(unit_resulting_resolution,[],[f204,f936,f149])).

fof(f149,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f77,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',antisymmetry_r2_hidden)).

fof(f973,plain,
    ( ~ spl8_0
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_82
    | spl8_113
    | ~ spl8_120 ),
    inference(avatar_contradiction_clause,[],[f972])).

fof(f972,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_82
    | ~ spl8_113
    | ~ spl8_120 ),
    inference(subsumption_resolution,[],[f971,f865])).

fof(f865,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl8_120 ),
    inference(avatar_component_clause,[],[f864])).

fof(f864,plain,
    ( spl8_120
  <=> m1_subset_1(sK4(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_120])])).

fof(f971,plain,
    ( ~ m1_subset_1(sK4(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_82
    | ~ spl8_113 ),
    inference(unit_resulting_resolution,[],[f89,f110,f131,f698,f834,f66])).

fof(f834,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK2,sK3),sK3)
    | ~ spl8_113 ),
    inference(avatar_component_clause,[],[f833])).

fof(f833,plain,
    ( spl8_113
  <=> ~ r1_orders_2(sK0,sK4(sK0,sK2,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f698,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),sK2)
    | ~ spl8_82 ),
    inference(avatar_component_clause,[],[f697])).

fof(f697,plain,
    ( spl8_82
  <=> r2_hidden(sK4(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f968,plain,
    ( ~ spl8_135
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_70
    | spl8_97
    | ~ spl8_108 ),
    inference(avatar_split_clause,[],[f954,f813,f771,f550,f109,f88,f966])).

fof(f550,plain,
    ( spl8_70
  <=> r1_lattice3(sK0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f771,plain,
    ( spl8_97
  <=> ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f813,plain,
    ( spl8_108
  <=> m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).

fof(f954,plain,
    ( ~ r2_hidden(sK5(sK0,sK1,sK3),k1_xboole_0)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_70
    | ~ spl8_97
    | ~ spl8_108 ),
    inference(unit_resulting_resolution,[],[f89,f551,f110,f772,f814,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f814,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl8_108 ),
    inference(avatar_component_clause,[],[f813])).

fof(f772,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl8_97 ),
    inference(avatar_component_clause,[],[f771])).

fof(f551,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK3)
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f550])).

fof(f951,plain,
    ( spl8_132
    | ~ spl8_124 ),
    inference(avatar_split_clause,[],[f919,f914,f949])).

fof(f949,plain,
    ( spl8_132
  <=> m1_subset_1(sK5(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_132])])).

fof(f914,plain,
    ( spl8_124
  <=> r2_hidden(sK5(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_124])])).

fof(f919,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),sK2)
    | ~ spl8_124 ),
    inference(unit_resulting_resolution,[],[f915,f76])).

fof(f915,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3),sK2)
    | ~ spl8_124 ),
    inference(avatar_component_clause,[],[f914])).

fof(f944,plain,
    ( ~ spl8_131
    | ~ spl8_124 ),
    inference(avatar_split_clause,[],[f918,f914,f942])).

fof(f942,plain,
    ( spl8_131
  <=> ~ r2_hidden(sK2,sK5(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_131])])).

fof(f918,plain,
    ( ~ r2_hidden(sK2,sK5(sK0,sK2,sK3))
    | ~ spl8_124 ),
    inference(unit_resulting_resolution,[],[f915,f75])).

fof(f937,plain,
    ( spl8_128
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f905,f166,f117,f935])).

fof(f117,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f166,plain,
    ( spl8_18
  <=> r2_hidden(sK4(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f905,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK2)
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f118,f167,f81])).

fof(f167,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f118,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f930,plain,
    ( ~ spl8_127
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f902,f166,f928])).

fof(f928,plain,
    ( spl8_127
  <=> ~ r2_hidden(sK1,sK4(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_127])])).

fof(f902,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1,sK3))
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f167,f75])).

fof(f916,plain,
    ( spl8_124
    | ~ spl8_0
    | ~ spl8_6
    | spl8_11 ),
    inference(avatar_split_clause,[],[f895,f121,f109,f88,f914])).

fof(f895,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3),sK2)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f89,f110,f122,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f892,plain,
    ( ~ spl8_18
    | spl8_115 ),
    inference(avatar_contradiction_clause,[],[f891])).

fof(f891,plain,
    ( $false
    | ~ spl8_18
    | ~ spl8_115 ),
    inference(subsumption_resolution,[],[f167,f875])).

fof(f875,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ spl8_115 ),
    inference(unit_resulting_resolution,[],[f844,f76])).

fof(f844,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),sK1)
    | ~ spl8_115 ),
    inference(avatar_component_clause,[],[f843])).

fof(f843,plain,
    ( spl8_115
  <=> ~ m1_subset_1(sK4(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f890,plain,
    ( ~ spl8_0
    | ~ spl8_6
    | ~ spl8_10
    | spl8_97
    | ~ spl8_108
    | ~ spl8_122 ),
    inference(avatar_contradiction_clause,[],[f889])).

fof(f889,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_97
    | ~ spl8_108
    | ~ spl8_122 ),
    inference(subsumption_resolution,[],[f888,f814])).

fof(f888,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_10
    | ~ spl8_97
    | ~ spl8_122 ),
    inference(unit_resulting_resolution,[],[f89,f110,f125,f872,f772,f70])).

fof(f125,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl8_10
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f873,plain,
    ( spl8_122
    | spl8_25
    | ~ spl8_104 ),
    inference(avatar_split_clause,[],[f828,f799,f203,f871])).

fof(f799,plain,
    ( spl8_104
  <=> m1_subset_1(sK5(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f828,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK2)
    | ~ spl8_25
    | ~ spl8_104 ),
    inference(unit_resulting_resolution,[],[f204,f800,f77])).

fof(f800,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),sK2)
    | ~ spl8_104 ),
    inference(avatar_component_clause,[],[f799])).

fof(f866,plain,
    ( spl8_120
    | ~ spl8_0
    | ~ spl8_6
    | spl8_13 ),
    inference(avatar_split_clause,[],[f620,f127,f109,f88,f864])).

fof(f127,plain,
    ( spl8_13
  <=> ~ r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f620,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f89,f110,f128,f67])).

fof(f128,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f859,plain,
    ( ~ spl8_119
    | spl8_25
    | ~ spl8_104 ),
    inference(avatar_split_clause,[],[f827,f799,f203,f857])).

fof(f857,plain,
    ( spl8_119
  <=> ~ r2_hidden(sK2,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_119])])).

fof(f827,plain,
    ( ~ r2_hidden(sK2,sK5(sK0,sK1,sK3))
    | ~ spl8_25
    | ~ spl8_104 ),
    inference(unit_resulting_resolution,[],[f204,f800,f149])).

fof(f852,plain,
    ( ~ spl8_117
    | spl8_53
    | spl8_89 ),
    inference(avatar_split_clause,[],[f765,f725,f384,f850])).

fof(f850,plain,
    ( spl8_117
  <=> ~ m1_subset_1(sK5(sK0,k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).

fof(f725,plain,
    ( spl8_89
  <=> ~ r2_hidden(sK5(sK0,k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f765,plain,
    ( ~ m1_subset_1(sK5(sK0,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl8_53
    | ~ spl8_89 ),
    inference(unit_resulting_resolution,[],[f385,f726,f77])).

fof(f726,plain,
    ( ~ r2_hidden(sK5(sK0,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl8_89 ),
    inference(avatar_component_clause,[],[f725])).

fof(f845,plain,
    ( ~ spl8_115
    | spl8_19
    | spl8_23 ),
    inference(avatar_split_clause,[],[f634,f195,f163,f843])).

fof(f163,plain,
    ( spl8_19
  <=> ~ r2_hidden(sK4(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f195,plain,
    ( spl8_23
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f634,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),sK1)
    | ~ spl8_19
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f196,f164,f77])).

fof(f164,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f163])).

fof(f196,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f835,plain,
    ( ~ spl8_113
    | ~ spl8_0
    | ~ spl8_6
    | spl8_13 ),
    inference(avatar_split_clause,[],[f619,f127,f109,f88,f833])).

fof(f619,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK2,sK3),sK3)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f89,f110,f128,f69])).

fof(f822,plain,
    ( spl8_110
    | ~ spl8_82 ),
    inference(avatar_split_clause,[],[f743,f697,f820])).

fof(f820,plain,
    ( spl8_110
  <=> m1_subset_1(sK4(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_110])])).

fof(f743,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK3),sK2)
    | ~ spl8_82 ),
    inference(unit_resulting_resolution,[],[f698,f76])).

fof(f815,plain,
    ( spl8_108
    | ~ spl8_0
    | ~ spl8_6
    | spl8_15 ),
    inference(avatar_split_clause,[],[f493,f137,f109,f88,f813])).

fof(f137,plain,
    ( spl8_15
  <=> ~ r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f493,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f89,f110,f138,f71])).

fof(f138,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f808,plain,
    ( ~ spl8_107
    | ~ spl8_82 ),
    inference(avatar_split_clause,[],[f742,f697,f806])).

fof(f806,plain,
    ( spl8_107
  <=> ~ r2_hidden(sK2,sK4(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_107])])).

fof(f742,plain,
    ( ~ r2_hidden(sK2,sK4(sK0,sK2,sK3))
    | ~ spl8_82 ),
    inference(unit_resulting_resolution,[],[f698,f75])).

fof(f801,plain,
    ( spl8_104
    | ~ spl8_8
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f659,f177,f117,f799])).

fof(f177,plain,
    ( spl8_20
  <=> r2_hidden(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f659,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),sK2)
    | ~ spl8_8
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f118,f178,f81])).

fof(f178,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f177])).

fof(f794,plain,
    ( spl8_102
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f657,f177,f792])).

fof(f792,plain,
    ( spl8_102
  <=> m1_subset_1(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f657,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f178,f76])).

fof(f787,plain,
    ( ~ spl8_101
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f656,f177,f785])).

fof(f785,plain,
    ( spl8_101
  <=> ~ r2_hidden(sK1,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f656,plain,
    ( ~ r2_hidden(sK1,sK5(sK0,sK1,sK3))
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f178,f75])).

fof(f780,plain,
    ( ~ spl8_99
    | spl8_75 ),
    inference(avatar_split_clause,[],[f629,f566,f778])).

fof(f778,plain,
    ( spl8_99
  <=> ~ r2_hidden(sK1,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).

fof(f566,plain,
    ( spl8_75
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_75])])).

fof(f629,plain,
    ( ~ r2_hidden(sK1,sK6(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl8_75 ),
    inference(unit_resulting_resolution,[],[f74,f567,f81])).

fof(f567,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_75 ),
    inference(avatar_component_clause,[],[f566])).

fof(f773,plain,
    ( ~ spl8_97
    | ~ spl8_0
    | ~ spl8_6
    | spl8_15 ),
    inference(avatar_split_clause,[],[f492,f137,f109,f88,f771])).

fof(f492,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f89,f110,f138,f73])).

fof(f761,plain,
    ( ~ spl8_95
    | spl8_73 ),
    inference(avatar_split_clause,[],[f562,f559,f759])).

fof(f759,plain,
    ( spl8_95
  <=> ~ r2_hidden(k1_xboole_0,sK6(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_95])])).

fof(f559,plain,
    ( spl8_73
  <=> ~ m1_subset_1(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_73])])).

fof(f562,plain,
    ( ~ r2_hidden(k1_xboole_0,sK6(k1_zfmisc_1(sK1)))
    | ~ spl8_73 ),
    inference(unit_resulting_resolution,[],[f74,f560,f81])).

fof(f560,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ spl8_73 ),
    inference(avatar_component_clause,[],[f559])).

fof(f754,plain,
    ( ~ spl8_93
    | spl8_37 ),
    inference(avatar_split_clause,[],[f270,f267,f752])).

fof(f752,plain,
    ( spl8_93
  <=> ~ r2_hidden(sK2,sK6(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_93])])).

fof(f267,plain,
    ( spl8_37
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f270,plain,
    ( ~ r2_hidden(sK2,sK6(k1_zfmisc_1(sK1)))
    | ~ spl8_37 ),
    inference(unit_resulting_resolution,[],[f74,f268,f81])).

fof(f268,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f267])).

fof(f737,plain,
    ( ~ spl8_91
    | spl8_65 ),
    inference(avatar_split_clause,[],[f527,f524,f735])).

fof(f735,plain,
    ( spl8_91
  <=> ~ r2_hidden(k1_xboole_0,sK6(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f524,plain,
    ( spl8_65
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f527,plain,
    ( ~ r2_hidden(k1_xboole_0,sK6(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl8_65 ),
    inference(unit_resulting_resolution,[],[f74,f525,f81])).

fof(f525,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_65 ),
    inference(avatar_component_clause,[],[f524])).

fof(f730,plain,
    ( spl8_88
    | ~ spl8_0
    | ~ spl8_6
    | spl8_71 ),
    inference(avatar_split_clause,[],[f625,f547,f109,f88,f728])).

fof(f728,plain,
    ( spl8_88
  <=> r2_hidden(sK5(sK0,k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f547,plain,
    ( spl8_71
  <=> ~ r1_lattice3(sK0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f625,plain,
    ( r2_hidden(sK5(sK0,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_71 ),
    inference(unit_resulting_resolution,[],[f89,f110,f548,f72])).

fof(f548,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK3)
    | ~ spl8_71 ),
    inference(avatar_component_clause,[],[f547])).

fof(f723,plain,
    ( ~ spl8_87
    | spl8_29 ),
    inference(avatar_split_clause,[],[f232,f225,f721])).

fof(f721,plain,
    ( spl8_87
  <=> ~ r2_hidden(sK2,sK6(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f225,plain,
    ( spl8_29
  <=> ~ m1_subset_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f232,plain,
    ( ~ r2_hidden(sK2,sK6(k1_zfmisc_1(sK2)))
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f74,f226,f81])).

fof(f226,plain,
    ( ~ m1_subset_1(sK2,sK2)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f225])).

fof(f716,plain,
    ( ~ spl8_85
    | spl8_27 ),
    inference(avatar_split_clause,[],[f229,f218,f714])).

fof(f714,plain,
    ( spl8_85
  <=> ~ r2_hidden(sK1,sK6(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).

fof(f218,plain,
    ( spl8_27
  <=> ~ m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f229,plain,
    ( ~ r2_hidden(sK1,sK6(k1_zfmisc_1(sK1)))
    | ~ spl8_27 ),
    inference(unit_resulting_resolution,[],[f74,f219,f81])).

fof(f219,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f218])).

fof(f699,plain,
    ( spl8_82
    | ~ spl8_0
    | ~ spl8_6
    | spl8_13 ),
    inference(avatar_split_clause,[],[f621,f127,f109,f88,f697])).

fof(f621,plain,
    ( r2_hidden(sK4(sK0,sK2,sK3),sK2)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f89,f110,f128,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f684,plain,
    ( spl8_80
    | spl8_53 ),
    inference(avatar_split_clause,[],[f603,f384,f682])).

fof(f682,plain,
    ( spl8_80
  <=> r2_hidden(sK6(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f603,plain,
    ( r2_hidden(sK6(k1_xboole_0),k1_xboole_0)
    | ~ spl8_53 ),
    inference(unit_resulting_resolution,[],[f74,f385,f77])).

fof(f677,plain,
    ( ~ spl8_79
    | spl8_53 ),
    inference(avatar_split_clause,[],[f602,f384,f675])).

fof(f675,plain,
    ( spl8_79
  <=> ~ r2_hidden(k1_xboole_0,sK6(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_79])])).

fof(f602,plain,
    ( ~ r2_hidden(k1_xboole_0,sK6(k1_xboole_0))
    | ~ spl8_53 ),
    inference(unit_resulting_resolution,[],[f74,f385,f149])).

fof(f642,plain,
    ( ~ spl8_77
    | spl8_75 ),
    inference(avatar_split_clause,[],[f630,f566,f640])).

fof(f640,plain,
    ( spl8_77
  <=> ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f630,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_75 ),
    inference(unit_resulting_resolution,[],[f567,f76])).

fof(f596,plain,
    ( spl8_23
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(avatar_contradiction_clause,[],[f595])).

fof(f595,plain,
    ( $false
    | ~ spl8_23
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(subsumption_resolution,[],[f574,f196])).

fof(f574,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f74,f573,f77])).

fof(f573,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f388,f570,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',t5_subset)).

fof(f570,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f569])).

fof(f569,plain,
    ( spl8_74
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f388,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl8_52
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f594,plain,
    ( ~ spl8_0
    | ~ spl8_6
    | spl8_15
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_15
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(subsumption_resolution,[],[f580,f138])).

fof(f580,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f89,f110,f573,f72])).

fof(f592,plain,
    ( ~ spl8_0
    | ~ spl8_6
    | spl8_15
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(avatar_contradiction_clause,[],[f591])).

fof(f591,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_15
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(subsumption_resolution,[],[f583,f110])).

fof(f583,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl8_0
    | ~ spl8_15
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f89,f138,f573,f72])).

fof(f590,plain,
    ( ~ spl8_0
    | ~ spl8_6
    | spl8_15
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_15
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(subsumption_resolution,[],[f584,f89])).

fof(f584,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl8_6
    | ~ spl8_15
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f110,f138,f573,f72])).

fof(f588,plain,
    ( ~ spl8_0
    | ~ spl8_6
    | spl8_15
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_15
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f89,f110,f138,f573,f72])).

fof(f587,plain,
    ( spl8_23
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | ~ spl8_23
    | ~ spl8_52
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f74,f196,f573,f77])).

fof(f571,plain,
    ( spl8_74
    | ~ spl8_8
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f441,f200,f117,f569])).

fof(f200,plain,
    ( spl8_24
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f441,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_8
    | ~ spl8_24 ),
    inference(backward_demodulation,[],[f435,f118])).

fof(f435,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f201,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',t6_boole)).

fof(f201,plain,
    ( v1_xboole_0(sK2)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f200])).

fof(f561,plain,
    ( ~ spl8_73
    | ~ spl8_24
    | spl8_37 ),
    inference(avatar_split_clause,[],[f449,f267,f200,f559])).

fof(f449,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK1)
    | ~ spl8_24
    | ~ spl8_37 ),
    inference(backward_demodulation,[],[f435,f268])).

fof(f552,plain,
    ( spl8_70
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f442,f200,f124,f550])).

fof(f442,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK3)
    | ~ spl8_10
    | ~ spl8_24 ),
    inference(backward_demodulation,[],[f435,f125])).

fof(f545,plain,
    ( ~ spl8_69
    | ~ spl8_24
    | spl8_35 ),
    inference(avatar_split_clause,[],[f448,f254,f200,f543])).

fof(f543,plain,
    ( spl8_69
  <=> ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f254,plain,
    ( spl8_35
  <=> ~ r2_hidden(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f448,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl8_24
    | ~ spl8_35 ),
    inference(backward_demodulation,[],[f435,f255])).

fof(f255,plain,
    ( ~ r2_hidden(sK2,sK2)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f254])).

fof(f538,plain,
    ( ~ spl8_67
    | ~ spl8_24
    | spl8_33 ),
    inference(avatar_split_clause,[],[f447,f247,f200,f536])).

fof(f536,plain,
    ( spl8_67
  <=> ~ r2_hidden(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f247,plain,
    ( spl8_33
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f447,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1)
    | ~ spl8_24
    | ~ spl8_33 ),
    inference(backward_demodulation,[],[f435,f248])).

fof(f248,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f247])).

fof(f526,plain,
    ( ~ spl8_65
    | ~ spl8_24
    | spl8_29 ),
    inference(avatar_split_clause,[],[f445,f225,f200,f524])).

fof(f445,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl8_24
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f435,f226])).

fof(f515,plain,
    ( ~ spl8_0
    | ~ spl8_6
    | spl8_13
    | ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_13
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f507,f443])).

fof(f443,plain,
    ( ~ r2_lattice3(sK0,k1_xboole_0,sK3)
    | ~ spl8_13
    | ~ spl8_24 ),
    inference(backward_demodulation,[],[f435,f128])).

fof(f507,plain,
    ( r2_lattice3(sK0,k1_xboole_0,sK3)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f89,f110,f462,f68])).

fof(f462,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_24 ),
    inference(forward_demodulation,[],[f434,f435])).

fof(f434,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f201,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',t7_boole)).

fof(f505,plain,
    ( spl8_62
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f435,f200,f503])).

fof(f503,plain,
    ( spl8_62
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f490,plain,
    ( ~ spl8_61
    | ~ spl8_24
    | spl8_55 ),
    inference(avatar_split_clause,[],[f458,f401,f200,f488])).

fof(f488,plain,
    ( spl8_61
  <=> ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f401,plain,
    ( spl8_55
  <=> ~ r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f458,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_24
    | ~ spl8_55 ),
    inference(backward_demodulation,[],[f435,f402])).

fof(f402,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl8_55 ),
    inference(avatar_component_clause,[],[f401])).

fof(f474,plain,
    ( spl8_52
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f444,f200,f387])).

fof(f444,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_24 ),
    inference(backward_demodulation,[],[f435,f201])).

fof(f473,plain,
    ( spl8_58
    | ~ spl8_4
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f440,f200,f102,f471])).

fof(f471,plain,
    ( spl8_58
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f102,plain,
    ( spl8_4
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f440,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl8_4
    | ~ spl8_24 ),
    inference(backward_demodulation,[],[f435,f103])).

fof(f103,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f460,plain,
    ( ~ spl8_24
    | spl8_53 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_53 ),
    inference(subsumption_resolution,[],[f444,f385])).

fof(f426,plain,
    ( ~ spl8_24
    | ~ spl8_44 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_44 ),
    inference(subsumption_resolution,[],[f201,f317])).

fof(f317,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_44 ),
    inference(unit_resulting_resolution,[],[f299,f80])).

fof(f299,plain,
    ( r2_hidden(sK6(sK2),sK2)
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl8_44
  <=> r2_hidden(sK6(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f424,plain,
    ( ~ spl8_0
    | ~ spl8_6
    | spl8_15
    | ~ spl8_22 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_15
    | ~ spl8_22 ),
    inference(subsumption_resolution,[],[f419,f358])).

fof(f358,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK3)
    | ~ spl8_15
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f351,f138])).

fof(f351,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f193,f65])).

fof(f193,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl8_22
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f419,plain,
    ( r1_lattice3(sK0,k1_xboole_0,sK3)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f89,f110,f377,f72])).

fof(f377,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_22 ),
    inference(forward_demodulation,[],[f350,f351])).

fof(f350,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f193,f80])).

fof(f414,plain,
    ( spl8_56
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f351,f192,f412])).

fof(f412,plain,
    ( spl8_56
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f406,plain,
    ( spl8_54
    | ~ spl8_4
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f356,f192,f102,f404])).

fof(f404,plain,
    ( spl8_54
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f356,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ spl8_4
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f351,f103])).

fof(f389,plain,
    ( spl8_52
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f362,f192,f387])).

fof(f362,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_22 ),
    inference(backward_demodulation,[],[f351,f193])).

fof(f345,plain,
    ( spl8_50
    | spl8_25
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f329,f325,f203,f343])).

fof(f343,plain,
    ( spl8_50
  <=> r2_hidden(sK6(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f325,plain,
    ( spl8_46
  <=> m1_subset_1(sK6(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f329,plain,
    ( r2_hidden(sK6(sK1),sK2)
    | ~ spl8_25
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f204,f326,f77])).

fof(f326,plain,
    ( m1_subset_1(sK6(sK1),sK2)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f325])).

fof(f338,plain,
    ( ~ spl8_49
    | spl8_25
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f328,f325,f203,f336])).

fof(f336,plain,
    ( spl8_49
  <=> ~ r2_hidden(sK2,sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f328,plain,
    ( ~ r2_hidden(sK2,sK6(sK1))
    | ~ spl8_25
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f204,f326,f149])).

fof(f327,plain,
    ( spl8_46
    | ~ spl8_8
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f308,f284,f117,f325])).

fof(f284,plain,
    ( spl8_40
  <=> r2_hidden(sK6(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f308,plain,
    ( m1_subset_1(sK6(sK1),sK2)
    | ~ spl8_8
    | ~ spl8_40 ),
    inference(unit_resulting_resolution,[],[f118,f285,f81])).

fof(f285,plain,
    ( r2_hidden(sK6(sK1),sK1)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f284])).

fof(f300,plain,
    ( spl8_44
    | spl8_25 ),
    inference(avatar_split_clause,[],[f212,f203,f298])).

fof(f212,plain,
    ( r2_hidden(sK6(sK2),sK2)
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f74,f204,f77])).

fof(f293,plain,
    ( ~ spl8_43
    | spl8_25 ),
    inference(avatar_split_clause,[],[f211,f203,f291])).

fof(f291,plain,
    ( spl8_43
  <=> ~ r2_hidden(sK2,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f211,plain,
    ( ~ r2_hidden(sK2,sK6(sK2))
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f74,f204,f149])).

fof(f286,plain,
    ( spl8_40
    | spl8_23 ),
    inference(avatar_split_clause,[],[f208,f195,f284])).

fof(f208,plain,
    ( r2_hidden(sK6(sK1),sK1)
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f74,f196,f77])).

fof(f279,plain,
    ( ~ spl8_39
    | spl8_23 ),
    inference(avatar_split_clause,[],[f207,f195,f277])).

fof(f277,plain,
    ( spl8_39
  <=> ~ r2_hidden(sK1,sK6(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f207,plain,
    ( ~ r2_hidden(sK1,sK6(sK1))
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f74,f196,f149])).

fof(f269,plain,
    ( ~ spl8_37
    | spl8_23
    | spl8_33 ),
    inference(avatar_split_clause,[],[f259,f247,f195,f267])).

fof(f259,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl8_23
    | ~ spl8_33 ),
    inference(unit_resulting_resolution,[],[f196,f248,f77])).

fof(f256,plain,
    ( ~ spl8_35
    | spl8_29 ),
    inference(avatar_split_clause,[],[f234,f225,f254])).

fof(f234,plain,
    ( ~ r2_hidden(sK2,sK2)
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f226,f76])).

fof(f249,plain,
    ( ~ spl8_33
    | ~ spl8_8
    | spl8_29 ),
    inference(avatar_split_clause,[],[f233,f225,f117,f247])).

fof(f233,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl8_8
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f118,f226,f81])).

fof(f242,plain,
    ( ~ spl8_31
    | spl8_27 ),
    inference(avatar_split_clause,[],[f230,f218,f240])).

fof(f240,plain,
    ( spl8_31
  <=> ~ r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f230,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl8_27 ),
    inference(unit_resulting_resolution,[],[f219,f76])).

fof(f227,plain,
    ( ~ spl8_29
    | spl8_25 ),
    inference(avatar_split_clause,[],[f210,f203,f225])).

fof(f210,plain,
    ( ~ m1_subset_1(sK2,sK2)
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f204,f156])).

fof(f156,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f149,f77])).

fof(f220,plain,
    ( ~ spl8_27
    | spl8_23 ),
    inference(avatar_split_clause,[],[f206,f195,f218])).

fof(f206,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f196,f156])).

fof(f205,plain,
    ( ~ spl8_25
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f187,f166,f117,f203])).

fof(f187,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f118,f167,f82])).

fof(f197,plain,
    ( ~ spl8_23
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f185,f166,f195])).

fof(f185,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f167,f80])).

fof(f179,plain,
    ( spl8_20
    | ~ spl8_0
    | ~ spl8_6
    | spl8_15 ),
    inference(avatar_split_clause,[],[f171,f137,f109,f88,f177])).

fof(f171,plain,
    ( r2_hidden(sK5(sK0,sK1,sK3),sK1)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_15 ),
    inference(unit_resulting_resolution,[],[f89,f138,f110,f72])).

fof(f168,plain,
    ( spl8_18
    | ~ spl8_0
    | ~ spl8_6
    | spl8_17 ),
    inference(avatar_split_clause,[],[f160,f144,f109,f88,f166])).

fof(f160,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3),sK1)
    | ~ spl8_0
    | ~ spl8_6
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f89,f145,f110,f68])).

fof(f147,plain,
    ( ~ spl8_15
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f64,f144,f137])).

fof(f64,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ( ~ r2_lattice3(sK0,sK1,sK3)
        & r2_lattice3(sK0,sK2,sK3) )
      | ( ~ r1_lattice3(sK0,sK1,sK3)
        & r1_lattice3(sK0,sK2,sK3) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & r1_tarski(sK1,sK2)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ( ( ~ r2_lattice3(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3) )
                  | ( ~ r1_lattice3(X0,X1,X3)
                    & r1_lattice3(X0,X2,X3) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & r1_tarski(X1,X2) )
        & l1_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(sK0,X1,X3)
                  & r2_lattice3(sK0,X2,X3) )
                | ( ~ r1_lattice3(sK0,X1,X3)
                  & r1_lattice3(sK0,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(X0,X1,X3)
                  & r2_lattice3(X0,X2,X3) )
                | ( ~ r1_lattice3(X0,X1,X3)
                  & r1_lattice3(X0,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_tarski(X1,X2) )
     => ( ? [X3] :
            ( ( ( ~ r2_lattice3(X0,sK1,X3)
                & r2_lattice3(X0,sK2,X3) )
              | ( ~ r1_lattice3(X0,sK1,X3)
                & r1_lattice3(X0,sK2,X3) ) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & r1_tarski(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ~ r2_lattice3(X0,X1,X3)
              & r2_lattice3(X0,X2,X3) )
            | ( ~ r1_lattice3(X0,X1,X3)
              & r1_lattice3(X0,X2,X3) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ( ~ r2_lattice3(X0,X1,sK3)
            & r2_lattice3(X0,X2,sK3) )
          | ( ~ r1_lattice3(X0,X1,sK3)
            & r1_lattice3(X0,X2,sK3) ) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(X0,X1,X3)
                  & r2_lattice3(X0,X2,X3) )
                | ( ~ r1_lattice3(X0,X1,X3)
                  & r1_lattice3(X0,X2,X3) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_tarski(X1,X2) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( ( r2_lattice3(X0,X2,X3)
                   => r2_lattice3(X0,X1,X3) )
                  & ( r1_lattice3(X0,X2,X3)
                   => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',t9_yellow_0)).

fof(f146,plain,
    ( spl8_10
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f63,f144,f124])).

fof(f63,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f139,plain,
    ( ~ spl8_15
    | spl8_12 ),
    inference(avatar_split_clause,[],[f62,f130,f137])).

fof(f62,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f132,plain,
    ( spl8_10
    | spl8_12 ),
    inference(avatar_split_clause,[],[f61,f130,f124])).

fof(f61,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f119,plain,
    ( spl8_8
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f112,f102,f117])).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f103,f78])).

fof(f111,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f60,f109])).

fof(f60,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f104,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f59,f102])).

fof(f59,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f83,f95])).

fof(f95,plain,
    ( spl8_2
  <=> l1_orders_2(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f83,plain,(
    l1_orders_2(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    l1_orders_2(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f12,f56])).

fof(f56,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK7) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t9_yellow_0.p',existence_l1_orders_2)).

fof(f90,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f58,f88])).

fof(f58,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
