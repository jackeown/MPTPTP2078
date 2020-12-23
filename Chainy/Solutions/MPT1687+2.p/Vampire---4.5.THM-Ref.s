%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1687+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:29 EST 2020

% Result     : Theorem 20.36s
% Output     : Refutation 20.36s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 434 expanded)
%              Number of leaves         :   28 ( 152 expanded)
%              Depth                    :   18
%              Number of atoms          :  769 (2150 expanded)
%              Number of equality atoms :   64 ( 128 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14014,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f7318,f7322,f7326,f7330,f7334,f7453,f7457,f7470,f7486,f8350,f8354,f8355,f8669,f13557,f13868,f13998,f14005])).

fof(f14005,plain,
    ( ~ spl437_13
    | spl437_14
    | ~ spl437_21
    | ~ spl437_27
    | ~ spl437_64 ),
    inference(avatar_contradiction_clause,[],[f14004])).

fof(f14004,plain,
    ( $false
    | ~ spl437_13
    | spl437_14
    | ~ spl437_21
    | ~ spl437_27
    | ~ spl437_64 ),
    inference(subsumption_resolution,[],[f14003,f13871])).

fof(f13871,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl437_13
    | ~ spl437_21
    | ~ spl437_27 ),
    inference(subsumption_resolution,[],[f13870,f8349])).

fof(f8349,plain,
    ( v1_relat_1(sK2)
    | ~ spl437_13 ),
    inference(avatar_component_clause,[],[f8348])).

fof(f8348,plain,
    ( spl437_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_13])])).

fof(f13870,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl437_21
    | ~ spl437_27 ),
    inference(subsumption_resolution,[],[f13869,f8668])).

fof(f8668,plain,
    ( v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl437_21 ),
    inference(avatar_component_clause,[],[f8667])).

fof(f8667,plain,
    ( spl437_21
  <=> v4_relat_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_21])])).

fof(f13869,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl437_27 ),
    inference(resolution,[],[f10162,f6799])).

fof(f6799,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f4627])).

fof(f4627,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f4626])).

fof(f4626,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1487])).

fof(f1487,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f10162,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl437_27 ),
    inference(avatar_component_clause,[],[f10161])).

fof(f10161,plain,
    ( spl437_27
  <=> v1_partfun1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_27])])).

fof(f14003,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | ~ spl437_13
    | spl437_14
    | ~ spl437_64 ),
    inference(forward_demodulation,[],[f13999,f8557])).

fof(f8557,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl437_13 ),
    inference(resolution,[],[f8349,f6197])).

fof(f6197,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f4220])).

fof(f4220,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f838])).

fof(f838,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f13999,plain,
    ( u1_struct_0(sK0) != k2_relat_1(k4_relat_1(sK2))
    | spl437_14
    | ~ spl437_64 ),
    inference(superposition,[],[f8353,f13478])).

fof(f13478,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl437_64 ),
    inference(avatar_component_clause,[],[f13477])).

fof(f13477,plain,
    ( spl437_64
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_64])])).

fof(f8353,plain,
    ( u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | spl437_14 ),
    inference(avatar_component_clause,[],[f8352])).

fof(f8352,plain,
    ( spl437_14
  <=> u1_struct_0(sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_14])])).

fof(f13998,plain,
    ( spl437_64
    | ~ spl437_1
    | ~ spl437_10
    | ~ spl437_13 ),
    inference(avatar_split_clause,[],[f8413,f8348,f7477,f7316,f13477])).

fof(f7316,plain,
    ( spl437_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_1])])).

fof(f7477,plain,
    ( spl437_10
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_10])])).

fof(f8413,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl437_1
    | ~ spl437_10
    | ~ spl437_13 ),
    inference(subsumption_resolution,[],[f8412,f8349])).

fof(f8412,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl437_1
    | ~ spl437_10 ),
    inference(subsumption_resolution,[],[f8368,f7317])).

fof(f7317,plain,
    ( v1_funct_1(sK2)
    | ~ spl437_1 ),
    inference(avatar_component_clause,[],[f7316])).

fof(f8368,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl437_10 ),
    inference(resolution,[],[f7478,f4975])).

fof(f4975,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f3488])).

fof(f3488,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f3487])).

fof(f3487,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f906])).

fof(f906,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f7478,plain,
    ( v2_funct_1(sK2)
    | ~ spl437_10 ),
    inference(avatar_component_clause,[],[f7477])).

fof(f13868,plain,
    ( spl437_27
    | ~ spl437_1
    | ~ spl437_9
    | ~ spl437_12
    | spl437_19 ),
    inference(avatar_split_clause,[],[f10170,f8655,f7484,f7468,f7316,f10161])).

fof(f7468,plain,
    ( spl437_9
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_9])])).

fof(f7484,plain,
    ( spl437_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_12])])).

fof(f8655,plain,
    ( spl437_19
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_19])])).

fof(f10170,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl437_1
    | ~ spl437_9
    | ~ spl437_12
    | spl437_19 ),
    inference(subsumption_resolution,[],[f10169,f7469])).

fof(f7469,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl437_9 ),
    inference(avatar_component_clause,[],[f7468])).

fof(f10169,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl437_1
    | ~ spl437_12
    | spl437_19 ),
    inference(subsumption_resolution,[],[f10168,f7317])).

fof(f10168,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl437_12
    | spl437_19 ),
    inference(subsumption_resolution,[],[f7737,f8656])).

fof(f8656,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl437_19 ),
    inference(avatar_component_clause,[],[f8655])).

fof(f7737,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ spl437_12 ),
    inference(resolution,[],[f7485,f6671])).

fof(f6671,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f4529])).

fof(f4529,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f4528])).

fof(f4528,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1475])).

fof(f1475,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f7485,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl437_12 ),
    inference(avatar_component_clause,[],[f7484])).

fof(f13557,plain,
    ( spl437_2
    | ~ spl437_6
    | ~ spl437_19 ),
    inference(avatar_contradiction_clause,[],[f13556])).

fof(f13556,plain,
    ( $false
    | spl437_2
    | ~ spl437_6
    | ~ spl437_19 ),
    inference(subsumption_resolution,[],[f13555,f7321])).

fof(f7321,plain,
    ( ~ v2_struct_0(sK1)
    | spl437_2 ),
    inference(avatar_component_clause,[],[f7320])).

fof(f7320,plain,
    ( spl437_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_2])])).

fof(f13555,plain,
    ( v2_struct_0(sK1)
    | ~ spl437_6
    | ~ spl437_19 ),
    inference(subsumption_resolution,[],[f13537,f7452])).

fof(f7452,plain,
    ( l1_struct_0(sK1)
    | ~ spl437_6 ),
    inference(avatar_component_clause,[],[f7451])).

fof(f7451,plain,
    ( spl437_6
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_6])])).

fof(f13537,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl437_19 ),
    inference(resolution,[],[f13178,f6647])).

fof(f6647,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4497])).

fof(f4497,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4496])).

fof(f4496,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f13178,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl437_19 ),
    inference(avatar_component_clause,[],[f8655])).

fof(f8669,plain,
    ( spl437_21
    | ~ spl437_12 ),
    inference(avatar_split_clause,[],[f7742,f7484,f8667])).

fof(f7742,plain,
    ( v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ spl437_12 ),
    inference(resolution,[],[f7485,f6736])).

fof(f6736,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f4599])).

fof(f4599,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f1211,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f8355,plain,
    ( spl437_10
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(avatar_split_clause,[],[f7785,f7484,f7468,f7455,f7332,f7328,f7324,f7320,f7316,f7477])).

fof(f7324,plain,
    ( spl437_3
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_3])])).

fof(f7328,plain,
    ( spl437_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_4])])).

fof(f7332,plain,
    ( spl437_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_5])])).

fof(f7455,plain,
    ( spl437_7
  <=> v23_waybel_0(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl437_7])])).

fof(f7785,plain,
    ( v2_funct_1(sK2)
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7784,f7456])).

fof(f7456,plain,
    ( v23_waybel_0(sK2,sK0,sK1)
    | ~ spl437_7 ),
    inference(avatar_component_clause,[],[f7455])).

fof(f7784,plain,
    ( ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7783,f7469])).

fof(f7783,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7782,f7317])).

fof(f7782,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7781,f7329])).

fof(f7329,plain,
    ( ~ v2_struct_0(sK0)
    | spl437_4 ),
    inference(avatar_component_clause,[],[f7328])).

fof(f7781,plain,
    ( v2_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | spl437_2
    | ~ spl437_3
    | ~ spl437_5
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7780,f7325])).

fof(f7325,plain,
    ( l1_orders_2(sK1)
    | ~ spl437_3 ),
    inference(avatar_component_clause,[],[f7324])).

fof(f7780,plain,
    ( ~ l1_orders_2(sK1)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | spl437_2
    | ~ spl437_5
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7779,f7321])).

fof(f7779,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | ~ spl437_5
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7488,f7333])).

fof(f7333,plain,
    ( l1_orders_2(sK0)
    | ~ spl437_5 ),
    inference(avatar_component_clause,[],[f7332])).

fof(f7488,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | v2_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | v2_funct_1(sK2)
    | ~ spl437_12 ),
    inference(resolution,[],[f7485,f4983])).

fof(f4983,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | v2_struct_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v23_waybel_0(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3496])).

fof(f3496,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v5_orders_3(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v2_funct_1(X2)
            & v1_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) )
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3495])).

fof(f3495,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v5_orders_3(X2,X0,X1)
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
            & v2_funct_1(X2)
            & v1_funct_1(X2) )
          | ~ v23_waybel_0(X2,X0,X1)
          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) )
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3155])).

fof(f3155,axiom,(
    ! [X0,X1] :
      ( ( l1_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
         => ( ( v23_waybel_0(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
           => ( v5_orders_3(X2,X0,X1)
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v2_funct_1(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc9_waybel_0)).

fof(f8354,plain,
    ( ~ spl437_14
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(avatar_split_clause,[],[f8030,f7484,f7468,f7455,f7332,f7328,f7324,f7320,f7316,f8352])).

fof(f8030,plain,
    ( u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f8025,f8029])).

fof(f8029,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f8028,f7806])).

fof(f7806,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7805,f7456])).

fof(f7805,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7804,f7329])).

fof(f7804,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | ~ spl437_5
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7803,f7469])).

fof(f7803,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | ~ spl437_5
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7802,f7317])).

fof(f7802,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | spl437_2
    | ~ spl437_3
    | ~ spl437_5
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7801,f7325])).

fof(f7801,plain,
    ( ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | spl437_2
    | ~ spl437_5
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7800,f7321])).

fof(f7800,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl437_5
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7495,f7333])).

fof(f7495,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v23_waybel_0(sK2,sK0,sK1)
    | ~ spl437_12 ),
    inference(resolution,[],[f7485,f4992])).

fof(f4992,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X1)
      | ~ l1_orders_2(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v23_waybel_0(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f3498])).

fof(f3498,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v23_waybel_0(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3497])).

fof(f3497,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v23_waybel_0(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ! [X4] :
                          ( ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) )
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3296])).

fof(f3296,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( r1_orders_2(X0,X3,X4)
                          <=> r1_orders_2(X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3),k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X4)) ) ) )
                  & u1_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v2_funct_1(X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_waybel_0)).

fof(f8028,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f8027,f7785])).

fof(f8027,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl437_1
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f8026,f7317])).

fof(f8026,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7556,f7469])).

fof(f7556,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl437_12 ),
    inference(resolution,[],[f7485,f4939])).

fof(f4939,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f3456])).

fof(f3456,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3455])).

fof(f3455,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1660])).

fof(f1660,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f8025,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f8020,f8024])).

fof(f8024,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f8023,f7806])).

fof(f8023,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f8022,f7785])).

fof(f8022,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl437_1
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f8021,f7317])).

fof(f8021,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7555,f7469])).

fof(f7555,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl437_12 ),
    inference(resolution,[],[f7485,f4938])).

fof(f4938,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f3456])).

fof(f8020,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f4809,f8019])).

fof(f8019,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f8018,f7806])).

fof(f8018,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl437_1
    | spl437_2
    | ~ spl437_3
    | spl437_4
    | ~ spl437_5
    | ~ spl437_7
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f8017,f7785])).

fof(f8017,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl437_1
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f8016,f7317])).

fof(f8016,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl437_9
    | ~ spl437_12 ),
    inference(subsumption_resolution,[],[f7554,f7469])).

fof(f7554,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl437_12 ),
    inference(resolution,[],[f7485,f4937])).

fof(f4937,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f3456])).

fof(f4809,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f3352])).

fof(f3352,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( u1_struct_0(X0) != k2_relat_1(k2_funct_1(X2))
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3351])).

fof(f3351,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( u1_struct_0(X0) != k2_relat_1(k2_funct_1(X2))
                | ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                | ~ v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                | ~ v1_funct_1(k2_funct_1(X2)) )
              & v23_waybel_0(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3298])).

fof(f3298,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v23_waybel_0(X2,X0,X1)
                 => ( u1_struct_0(X0) = k2_relat_1(k2_funct_1(X2))
                    & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                    & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                    & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3297])).

fof(f3297,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v23_waybel_0(X2,X0,X1)
               => ( u1_struct_0(X0) = k2_relat_1(k2_funct_1(X2))
                  & m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(k2_funct_1(X2),u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(k2_funct_1(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_waybel_0)).

fof(f8350,plain,
    ( spl437_13
    | ~ spl437_12 ),
    inference(avatar_split_clause,[],[f7561,f7484,f8348])).

fof(f7561,plain,
    ( v1_relat_1(sK2)
    | ~ spl437_12 ),
    inference(resolution,[],[f7485,f5034])).

fof(f5034,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f3526])).

fof(f3526,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f7486,plain,(
    spl437_12 ),
    inference(avatar_split_clause,[],[f4812,f7484])).

fof(f4812,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f3352])).

fof(f7470,plain,(
    spl437_9 ),
    inference(avatar_split_clause,[],[f4811,f7468])).

fof(f4811,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f3352])).

fof(f7457,plain,(
    spl437_7 ),
    inference(avatar_split_clause,[],[f4813,f7455])).

fof(f4813,plain,(
    v23_waybel_0(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f3352])).

fof(f7453,plain,
    ( spl437_6
    | ~ spl437_3 ),
    inference(avatar_split_clause,[],[f7434,f7324,f7451])).

fof(f7434,plain,
    ( l1_struct_0(sK1)
    | ~ spl437_3 ),
    inference(resolution,[],[f7325,f6648])).

fof(f6648,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4498])).

fof(f4498,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1895])).

fof(f1895,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f7334,plain,(
    spl437_5 ),
    inference(avatar_split_clause,[],[f4817,f7332])).

fof(f4817,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f3352])).

fof(f7330,plain,(
    ~ spl437_4 ),
    inference(avatar_split_clause,[],[f4816,f7328])).

fof(f4816,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3352])).

fof(f7326,plain,(
    spl437_3 ),
    inference(avatar_split_clause,[],[f4815,f7324])).

fof(f4815,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f3352])).

fof(f7322,plain,(
    ~ spl437_2 ),
    inference(avatar_split_clause,[],[f4814,f7320])).

fof(f4814,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3352])).

fof(f7318,plain,(
    spl437_1 ),
    inference(avatar_split_clause,[],[f4810,f7316])).

fof(f4810,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f3352])).
%------------------------------------------------------------------------------
