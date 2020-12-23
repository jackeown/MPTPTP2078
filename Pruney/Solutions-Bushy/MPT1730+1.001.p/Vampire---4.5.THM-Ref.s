%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1730+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:26 EST 2020

% Result     : Theorem 3.25s
% Output     : Refutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  306 ( 832 expanded)
%              Number of leaves         :   65 ( 394 expanded)
%              Depth                    :    9
%              Number of atoms          : 1072 (3858 expanded)
%              Number of equality atoms :   50 ( 141 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f115,f120,f130,f135,f140,f145,f150,f160,f165,f179,f185,f211,f213,f215,f221,f227,f233,f287,f297,f318,f342,f371,f393,f398,f403,f408,f419,f435,f486,f519,f571,f816,f821,f830,f837,f841,f843,f849,f853,f861,f869,f875,f1899,f4192,f4236,f4238,f4239,f4783,f4832,f4833,f4873,f4879,f4880,f5152,f5188])).

fof(f5188,plain,
    ( ~ spl8_1
    | ~ spl8_4
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(avatar_contradiction_clause,[],[f5187])).

fof(f5187,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f5178,f105])).

fof(f105,plain,
    ( r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl8_4
  <=> r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f5178,plain,
    ( ~ r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_1
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f232,f291,f93,f377])).

fof(f377,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tsep_1(X4,k1_tsep_1(X7,X6,X5))
      | ~ sP0(X4,X5,X6,X7)
      | ~ l1_struct_0(k1_tsep_1(X7,X6,X5))
      | ~ l1_struct_0(X4) ) ),
    inference(resolution,[],[f56,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tsep_1(X1,X0)
        & r1_tsep_1(X2,X0)
        & ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ( r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3)
        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ( r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3)
        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f93,plain,
    ( sP0(sK7,sK6,sK5,sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_1
  <=> sP0(sK7,sK6,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f291,plain,
    ( l1_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl8_28
  <=> l1_struct_0(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f232,plain,
    ( l1_struct_0(sK7)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl8_25
  <=> l1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f5152,plain,
    ( spl8_242
    | ~ spl8_36
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f5114,f432,f390,f1903])).

fof(f1903,plain,
    ( spl8_242
  <=> r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_242])])).

fof(f390,plain,
    ( spl8_36
  <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f432,plain,
    ( spl8_42
  <=> k1_xboole_0 = k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f5114,plain,
    ( r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))
    | ~ spl8_36
    | ~ spl8_42 ),
    inference(unit_resulting_resolution,[],[f391,f433,f2294])).

fof(f2294,plain,(
    ! [X14,X12,X13] :
      ( r1_xboole_0(X12,k2_xboole_0(X13,X14))
      | k1_xboole_0 != k3_xboole_0(X12,X13)
      | ~ r1_xboole_0(X12,X14) ) ),
    inference(superposition,[],[f83,f459])).

fof(f459,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X3,X5) = k3_xboole_0(X3,k2_xboole_0(X5,X4))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(forward_demodulation,[],[f452,f71])).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f452,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X3,k2_xboole_0(X5,X4)) = k2_xboole_0(k3_xboole_0(X3,X5),k1_xboole_0)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f84,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f84,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f433,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f432])).

fof(f391,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f390])).

fof(f4880,plain,
    ( spl8_4
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15
    | ~ spl8_25
    | ~ spl8_28
    | ~ spl8_34
    | spl8_86
    | ~ spl8_87
    | ~ spl8_242 ),
    inference(avatar_split_clause,[],[f4719,f1903,f818,f813,f339,f290,f230,f157,f147,f142,f137,f132,f127,f103])).

fof(f127,plain,
    ( spl8_9
  <=> m1_pre_topc(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f132,plain,
    ( spl8_10
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f137,plain,
    ( spl8_11
  <=> m1_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f142,plain,
    ( spl8_12
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f147,plain,
    ( spl8_13
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f157,plain,
    ( spl8_15
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f339,plain,
    ( spl8_34
  <=> m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f813,plain,
    ( spl8_86
  <=> v2_struct_0(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f818,plain,
    ( spl8_87
  <=> v1_pre_topc(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f4719,plain,
    ( r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15
    | ~ spl8_25
    | ~ spl8_28
    | ~ spl8_34
    | spl8_86
    | ~ spl8_87
    | ~ spl8_242 ),
    inference(unit_resulting_resolution,[],[f159,f149,f144,f232,f134,f139,f129,f815,f820,f291,f340,f1904,f945])).

fof(f945,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_xboole_0(u1_struct_0(X11),k2_xboole_0(u1_struct_0(X9),u1_struct_0(X10)))
      | r1_tsep_1(X11,k1_tsep_1(X8,X9,X10))
      | ~ l1_struct_0(k1_tsep_1(X8,X9,X10))
      | ~ l1_struct_0(X11)
      | ~ m1_pre_topc(k1_tsep_1(X8,X9,X10),X8)
      | ~ v1_pre_topc(k1_tsep_1(X8,X9,X10))
      | v2_struct_0(k1_tsep_1(X8,X9,X10))
      | ~ m1_pre_topc(X10,X8)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X9,X8)
      | v2_struct_0(X9)
      | ~ l1_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(superposition,[],[f73,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f1904,plain,
    ( r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))
    | ~ spl8_242 ),
    inference(avatar_component_clause,[],[f1903])).

fof(f340,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f339])).

fof(f820,plain,
    ( v1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_87 ),
    inference(avatar_component_clause,[],[f818])).

fof(f815,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | spl8_86 ),
    inference(avatar_component_clause,[],[f813])).

fof(f129,plain,
    ( m1_pre_topc(sK6,sK4)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f139,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f134,plain,
    ( ~ v2_struct_0(sK6)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f144,plain,
    ( ~ v2_struct_0(sK5)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f149,plain,
    ( l1_pre_topc(sK4)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f159,plain,
    ( ~ v2_struct_0(sK4)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f157])).

fof(f4879,plain,
    ( ~ spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f4249,f103,f99])).

fof(f99,plain,
    ( spl8_3
  <=> sP1(sK6,sK7,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f4249,plain,
    ( ~ sP1(sK6,sK7,sK5,sK4)
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f105,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X1,k1_tsep_1(X3,X2,X0))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tsep_1(X1,X0)
        & r1_tsep_1(X1,X2)
        & ~ r1_tsep_1(X1,k1_tsep_1(X3,X2,X0)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X2,X3,X1,X0] :
      ( ( r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1)
        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
      | ~ sP1(X2,X3,X1,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X2,X3,X1,X0] :
      ( ( r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1)
        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
      | ~ sP1(X2,X3,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f4873,plain,
    ( ~ spl8_27
    | ~ spl8_2
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f4872,f273,f95,f278])).

fof(f278,plain,
    ( spl8_27
  <=> r1_tsep_1(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f95,plain,
    ( spl8_2
  <=> sP2(sK7,sK6,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f273,plain,
    ( spl8_26
  <=> r1_tsep_1(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f4872,plain,
    ( ~ r1_tsep_1(sK5,sK7)
    | ~ spl8_2
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f4246,f274])).

fof(f274,plain,
    ( r1_tsep_1(sK6,sK7)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f273])).

fof(f4246,plain,
    ( ~ r1_tsep_1(sK5,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ spl8_2 ),
    inference(resolution,[],[f97,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ r1_tsep_1(X2,X0)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
        & ( ~ r1_tsep_1(X1,X0)
          | ~ r1_tsep_1(X2,X0) ) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
        & ( ~ r1_tsep_1(X2,X3)
          | ~ r1_tsep_1(X1,X3) ) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
        & ( ~ r1_tsep_1(X2,X3)
          | ~ r1_tsep_1(X1,X3) ) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f97,plain,
    ( sP2(sK7,sK6,sK5,sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f4833,plain,
    ( ~ spl8_42
    | spl8_39 ),
    inference(avatar_split_clause,[],[f4276,f405,f432])).

fof(f405,plain,
    ( spl8_39
  <=> r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f4276,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | spl8_39 ),
    inference(unit_resulting_resolution,[],[f407,f254])).

fof(f254,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k3_xboole_0(X3,X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f83,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f407,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | spl8_39 ),
    inference(avatar_component_clause,[],[f405])).

fof(f4832,plain,
    ( spl8_42
    | ~ spl8_36
    | ~ spl8_242 ),
    inference(avatar_split_clause,[],[f4831,f1903,f390,f432])).

fof(f4831,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ spl8_36
    | ~ spl8_242 ),
    inference(subsumption_resolution,[],[f4737,f391])).

fof(f4737,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | k1_xboole_0 = k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ spl8_242 ),
    inference(resolution,[],[f1904,f2287])).

fof(f2287,plain,(
    ! [X6,X8,X7] :
      ( ~ r1_xboole_0(X6,k2_xboole_0(X7,X8))
      | ~ r1_xboole_0(X6,X8)
      | k1_xboole_0 = k3_xboole_0(X6,X7) ) ),
    inference(superposition,[],[f459,f82])).

fof(f4783,plain,
    ( spl8_44
    | ~ spl8_19
    | ~ spl8_242 ),
    inference(avatar_split_clause,[],[f4770,f1903,f182,f479])).

fof(f479,plain,
    ( spl8_44
  <=> v1_xboole_0(k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f182,plain,
    ( spl8_19
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f4770,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)))
    | ~ spl8_19
    | ~ spl8_242 ),
    inference(forward_demodulation,[],[f4721,f79])).

fof(f4721,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | ~ spl8_19
    | ~ spl8_242 ),
    inference(unit_resulting_resolution,[],[f1904,f2112])).

fof(f2112,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_xboole_0(X3,k2_xboole_0(X4,X5))
        | v1_xboole_0(k3_xboole_0(X3,X5)) )
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f2108,f184])).

fof(f184,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f2108,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k3_xboole_0(X3,X5))
      | ~ r1_xboole_0(X3,k2_xboole_0(X4,X5)) ) ),
    inference(superposition,[],[f457,f82])).

fof(f457,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_xboole_0(k3_xboole_0(X3,k2_xboole_0(X4,X5)))
      | v1_xboole_0(k3_xboole_0(X3,X5)) ) ),
    inference(superposition,[],[f80,f84])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_xboole_0(X1,X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
     => ~ v1_xboole_0(k2_xboole_0(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(f4239,plain,
    ( u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) != k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))
    | r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))
    | ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f4238,plain,
    ( ~ spl8_3
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f4237])).

fof(f4237,plain,
    ( $false
    | ~ spl8_3
    | spl8_5 ),
    inference(subsumption_resolution,[],[f4228,f110])).

fof(f110,plain,
    ( ~ r1_tsep_1(sK7,sK5)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl8_5
  <=> r1_tsep_1(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f4228,plain,
    ( r1_tsep_1(sK7,sK5)
    | ~ spl8_3 ),
    inference(resolution,[],[f101,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_tsep_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,
    ( sP1(sK6,sK7,sK5,sK4)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f4236,plain,
    ( ~ spl8_3
    | spl8_6 ),
    inference(avatar_contradiction_clause,[],[f4235])).

fof(f4235,plain,
    ( $false
    | ~ spl8_3
    | spl8_6 ),
    inference(subsumption_resolution,[],[f4227,f114])).

fof(f114,plain,
    ( ~ r1_tsep_1(sK7,sK6)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl8_6
  <=> r1_tsep_1(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f4227,plain,
    ( r1_tsep_1(sK7,sK6)
    | ~ spl8_3 ),
    inference(resolution,[],[f101,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4192,plain,
    ( ~ spl8_2
    | spl8_29 ),
    inference(avatar_split_clause,[],[f971,f294,f95])).

fof(f294,plain,
    ( spl8_29
  <=> r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f971,plain,
    ( ~ sP2(sK7,sK6,sK5,sK4)
    | spl8_29 ),
    inference(unit_resulting_resolution,[],[f296,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f296,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7)
    | spl8_29 ),
    inference(avatar_component_clause,[],[f294])).

fof(f1899,plain,
    ( spl8_241
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15
    | ~ spl8_34
    | spl8_86
    | ~ spl8_87 ),
    inference(avatar_split_clause,[],[f1752,f818,f813,f339,f157,f147,f142,f137,f132,f127,f1896])).

fof(f1896,plain,
    ( spl8_241
  <=> u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) = k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_241])])).

fof(f1752,plain,
    ( u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) = k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15
    | ~ spl8_34
    | spl8_86
    | ~ spl8_87 ),
    inference(unit_resulting_resolution,[],[f159,f149,f144,f134,f139,f129,f815,f820,f340,f89])).

fof(f875,plain,
    ( ~ spl8_39
    | ~ spl8_19
    | spl8_45 ),
    inference(avatar_split_clause,[],[f874,f512,f182,f405])).

fof(f512,plain,
    ( spl8_45
  <=> v1_xboole_0(k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f874,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | ~ spl8_19
    | spl8_45 ),
    inference(subsumption_resolution,[],[f522,f184])).

fof(f522,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | spl8_45 ),
    inference(superposition,[],[f514,f82])).

fof(f514,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7)))
    | spl8_45 ),
    inference(avatar_component_clause,[],[f512])).

fof(f869,plain,
    ( ~ spl8_37
    | ~ spl8_19
    | spl8_45 ),
    inference(avatar_split_clause,[],[f868,f512,f182,f395])).

fof(f395,plain,
    ( spl8_37
  <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f868,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ spl8_19
    | spl8_45 ),
    inference(subsumption_resolution,[],[f521,f184])).

fof(f521,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | spl8_45 ),
    inference(superposition,[],[f514,f249])).

fof(f249,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k3_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f82,f79])).

fof(f861,plain,
    ( ~ spl8_36
    | spl8_38 ),
    inference(avatar_split_clause,[],[f443,f400,f390])).

fof(f400,plain,
    ( spl8_38
  <=> r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f443,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_38 ),
    inference(unit_resulting_resolution,[],[f402,f261])).

fof(f261,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(trivial_inequality_removal,[],[f258])).

fof(f258,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(superposition,[],[f83,f249])).

fof(f402,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | spl8_38 ),
    inference(avatar_component_clause,[],[f400])).

fof(f853,plain,
    ( ~ spl8_27
    | ~ spl8_23
    | ~ spl8_25
    | spl8_39 ),
    inference(avatar_split_clause,[],[f460,f405,f230,f218,f278])).

fof(f218,plain,
    ( spl8_23
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f460,plain,
    ( ~ r1_tsep_1(sK5,sK7)
    | ~ spl8_23
    | ~ spl8_25
    | spl8_39 ),
    inference(unit_resulting_resolution,[],[f220,f232,f407,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f220,plain,
    ( l1_struct_0(sK5)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f218])).

fof(f849,plain,
    ( ~ spl8_5
    | ~ spl8_23
    | ~ spl8_25
    | spl8_37 ),
    inference(avatar_split_clause,[],[f425,f395,f230,f218,f108])).

fof(f425,plain,
    ( ~ r1_tsep_1(sK7,sK5)
    | ~ spl8_23
    | ~ spl8_25
    | spl8_37 ),
    inference(unit_resulting_resolution,[],[f232,f220,f397,f72])).

fof(f397,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | spl8_37 ),
    inference(avatar_component_clause,[],[f395])).

fof(f843,plain,
    ( ~ spl8_1
    | spl8_27 ),
    inference(avatar_contradiction_clause,[],[f842])).

fof(f842,plain,
    ( $false
    | ~ spl8_1
    | spl8_27 ),
    inference(subsumption_resolution,[],[f93,f307])).

fof(f307,plain,
    ( ! [X0,X1] : ~ sP0(sK7,X0,sK5,X1)
    | spl8_27 ),
    inference(unit_resulting_resolution,[],[f280,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f280,plain,
    ( ~ r1_tsep_1(sK5,sK7)
    | spl8_27 ),
    inference(avatar_component_clause,[],[f278])).

fof(f841,plain,
    ( ~ spl8_6
    | ~ spl8_24
    | ~ spl8_25
    | spl8_36 ),
    inference(avatar_split_clause,[],[f409,f390,f230,f224,f112])).

fof(f224,plain,
    ( spl8_24
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f409,plain,
    ( ~ r1_tsep_1(sK7,sK6)
    | ~ spl8_24
    | ~ spl8_25
    | spl8_36 ),
    inference(unit_resulting_resolution,[],[f232,f226,f392,f72])).

fof(f392,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_36 ),
    inference(avatar_component_clause,[],[f390])).

fof(f226,plain,
    ( l1_struct_0(sK6)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f224])).

fof(f837,plain,
    ( ~ spl8_1
    | spl8_26 ),
    inference(avatar_contradiction_clause,[],[f836])).

fof(f836,plain,
    ( $false
    | ~ spl8_1
    | spl8_26 ),
    inference(subsumption_resolution,[],[f93,f300])).

fof(f300,plain,
    ( ! [X0,X1] : ~ sP0(sK7,sK6,X0,X1)
    | spl8_26 ),
    inference(unit_resulting_resolution,[],[f275,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f275,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | spl8_26 ),
    inference(avatar_component_clause,[],[f273])).

fof(f830,plain,
    ( spl8_88
    | ~ spl8_4
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f823,f290,f230,f103,f827])).

fof(f827,plain,
    ( spl8_88
  <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f823,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | ~ spl8_4
    | ~ spl8_25
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f232,f105,f291,f72])).

fof(f821,plain,
    ( spl8_87
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f810,f367,f818])).

fof(f367,plain,
    ( spl8_35
  <=> sP3(sK4,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f810,plain,
    ( v1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f368,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f368,plain,
    ( sP3(sK4,sK6,sK5)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f367])).

fof(f816,plain,
    ( ~ spl8_86
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f811,f367,f813])).

fof(f811,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_35 ),
    inference(unit_resulting_resolution,[],[f368,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f571,plain,
    ( spl8_35
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(avatar_split_clause,[],[f537,f157,f147,f142,f137,f132,f127,f367])).

fof(f537,plain,
    ( sP3(sK4,sK6,sK5)
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(unit_resulting_resolution,[],[f159,f149,f144,f139,f134,f129,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f28,f33])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f519,plain,
    ( ~ spl8_45
    | spl8_42 ),
    inference(avatar_split_clause,[],[f518,f432,f512])).

fof(f518,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7)))
    | spl8_42 ),
    inference(forward_demodulation,[],[f499,f79])).

fof(f499,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5)))
    | spl8_42 ),
    inference(unit_resulting_resolution,[],[f434,f74])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f434,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | spl8_42 ),
    inference(avatar_component_clause,[],[f432])).

fof(f486,plain,
    ( ~ spl8_44
    | spl8_40 ),
    inference(avatar_split_clause,[],[f485,f416,f479])).

fof(f416,plain,
    ( spl8_40
  <=> k1_xboole_0 = k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f485,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)))
    | spl8_40 ),
    inference(forward_demodulation,[],[f466,f79])).

fof(f466,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | spl8_40 ),
    inference(unit_resulting_resolution,[],[f418,f74])).

fof(f418,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_40 ),
    inference(avatar_component_clause,[],[f416])).

fof(f435,plain,
    ( ~ spl8_42
    | spl8_37 ),
    inference(avatar_split_clause,[],[f428,f395,f432])).

fof(f428,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | spl8_37 ),
    inference(unit_resulting_resolution,[],[f397,f83])).

fof(f419,plain,
    ( ~ spl8_40
    | spl8_36 ),
    inference(avatar_split_clause,[],[f412,f390,f416])).

fof(f412,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_36 ),
    inference(unit_resulting_resolution,[],[f392,f83])).

fof(f408,plain,
    ( ~ spl8_39
    | ~ spl8_23
    | ~ spl8_25
    | spl8_27 ),
    inference(avatar_split_clause,[],[f382,f278,f230,f218,f405])).

fof(f382,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | ~ spl8_23
    | ~ spl8_25
    | spl8_27 ),
    inference(unit_resulting_resolution,[],[f220,f232,f280,f73])).

fof(f403,plain,
    ( ~ spl8_38
    | ~ spl8_24
    | ~ spl8_25
    | spl8_26 ),
    inference(avatar_split_clause,[],[f383,f273,f230,f224,f400])).

fof(f383,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl8_24
    | ~ spl8_25
    | spl8_26 ),
    inference(unit_resulting_resolution,[],[f226,f232,f275,f73])).

fof(f398,plain,
    ( ~ spl8_37
    | spl8_5
    | ~ spl8_23
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f384,f230,f218,f108,f395])).

fof(f384,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | spl8_5
    | ~ spl8_23
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f232,f220,f110,f73])).

fof(f393,plain,
    ( ~ spl8_36
    | spl8_6
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f385,f230,f224,f112,f390])).

fof(f385,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_6
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f232,f226,f114,f73])).

fof(f371,plain,
    ( ~ spl8_35
    | spl8_34 ),
    inference(avatar_split_clause,[],[f365,f339,f367])).

fof(f365,plain,
    ( ~ sP3(sK4,sK6,sK5)
    | spl8_34 ),
    inference(resolution,[],[f341,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f341,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4)
    | spl8_34 ),
    inference(avatar_component_clause,[],[f339])).

fof(f342,plain,
    ( ~ spl8_34
    | ~ spl8_13
    | spl8_30 ),
    inference(avatar_split_clause,[],[f319,f314,f147,f339])).

fof(f314,plain,
    ( spl8_30
  <=> l1_pre_topc(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f319,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4)
    | ~ spl8_13
    | spl8_30 ),
    inference(unit_resulting_resolution,[],[f149,f316,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f316,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | spl8_30 ),
    inference(avatar_component_clause,[],[f314])).

fof(f318,plain,
    ( ~ spl8_30
    | spl8_28 ),
    inference(avatar_split_clause,[],[f312,f290,f314])).

fof(f312,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | spl8_28 ),
    inference(resolution,[],[f292,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f292,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | spl8_28 ),
    inference(avatar_component_clause,[],[f290])).

fof(f297,plain,
    ( ~ spl8_28
    | ~ spl8_29
    | spl8_4
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f288,f230,f103,f294,f290])).

fof(f288,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7)
    | ~ l1_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | spl8_4
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f271,f232])).

fof(f271,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7)
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | spl8_4 ),
    inference(resolution,[],[f81,f104])).

fof(f104,plain,
    ( ~ r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f287,plain,
    ( ~ spl8_26
    | spl8_6
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f286,f230,f224,f112,f273])).

fof(f286,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | spl8_6
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f285,f226])).

fof(f285,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | ~ l1_struct_0(sK6)
    | spl8_6
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f270,f232])).

fof(f270,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(sK6)
    | spl8_6 ),
    inference(resolution,[],[f81,f114])).

fof(f233,plain,
    ( spl8_25
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f228,f206,f230])).

fof(f206,plain,
    ( spl8_22
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f228,plain,
    ( l1_struct_0(sK7)
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f208,f75])).

fof(f208,plain,
    ( l1_pre_topc(sK7)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f206])).

fof(f227,plain,
    ( spl8_24
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f222,f201,f224])).

fof(f201,plain,
    ( spl8_21
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f222,plain,
    ( l1_struct_0(sK6)
    | ~ spl8_21 ),
    inference(unit_resulting_resolution,[],[f203,f75])).

fof(f203,plain,
    ( l1_pre_topc(sK6)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f201])).

fof(f221,plain,
    ( spl8_23
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f216,f196,f218])).

fof(f196,plain,
    ( spl8_20
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f216,plain,
    ( l1_struct_0(sK5)
    | ~ spl8_20 ),
    inference(unit_resulting_resolution,[],[f198,f75])).

fof(f198,plain,
    ( l1_pre_topc(sK5)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f196])).

fof(f215,plain,
    ( spl8_20
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f214,f147,f137,f196])).

fof(f214,plain,
    ( l1_pre_topc(sK5)
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f194,f149])).

fof(f194,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ spl8_11 ),
    inference(resolution,[],[f76,f139])).

fof(f213,plain,
    ( spl8_21
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f212,f147,f127,f201])).

fof(f212,plain,
    ( l1_pre_topc(sK6)
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f193,f149])).

fof(f193,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK4)
    | ~ spl8_9 ),
    inference(resolution,[],[f76,f129])).

fof(f211,plain,
    ( spl8_22
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f210,f147,f117,f206])).

fof(f117,plain,
    ( spl8_7
  <=> m1_pre_topc(sK7,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f210,plain,
    ( l1_pre_topc(sK7)
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f192,f149])).

fof(f192,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK4)
    | ~ spl8_7 ),
    inference(resolution,[],[f76,f119])).

fof(f119,plain,
    ( m1_pre_topc(sK7,sK4)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f185,plain,
    ( spl8_19
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f180,f176,f162,f182])).

fof(f162,plain,
    ( spl8_16
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f176,plain,
    ( spl8_18
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f180,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f164,f178])).

fof(f178,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f164,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f162])).

fof(f179,plain,
    ( spl8_18
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f172,f162,f176])).

fof(f172,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl8_16 ),
    inference(unit_resulting_resolution,[],[f164,f74])).

fof(f165,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f70,f162])).

fof(f70,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f160,plain,(
    ~ spl8_15 ),
    inference(avatar_split_clause,[],[f59,f157])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ( r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
        & ( ~ r1_tsep_1(sK7,sK6)
          | ~ r1_tsep_1(sK7,sK5) ) )
      | sP1(sK6,sK7,sK5,sK4)
      | sP2(sK7,sK6,sK5,sK4)
      | sP0(sK7,sK6,sK5,sK4) )
    & m1_pre_topc(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f32,f44,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ( ~ r1_tsep_1(X3,X2)
                          | ~ r1_tsep_1(X3,X1) ) )
                      | sP1(X2,X3,X1,X0)
                      | sP2(X3,X2,X1,X0)
                      | sP0(X3,X2,X1,X0) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(sK4,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | sP1(X2,X3,X1,sK4)
                    | sP2(X3,X2,X1,sK4)
                    | sP0(X3,X2,X1,sK4) )
                  & m1_pre_topc(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( r1_tsep_1(X3,k1_tsep_1(sK4,X1,X2))
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1) ) )
                  | sP1(X2,X3,X1,sK4)
                  | sP2(X3,X2,X1,sK4)
                  | sP0(X3,X2,X1,sK4) )
                & m1_pre_topc(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK4)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK4)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( r1_tsep_1(X3,k1_tsep_1(sK4,sK5,X2))
                  & ( ~ r1_tsep_1(X3,X2)
                    | ~ r1_tsep_1(X3,sK5) ) )
                | sP1(X2,X3,sK5,sK4)
                | sP2(X3,X2,sK5,sK4)
                | sP0(X3,X2,sK5,sK4) )
              & m1_pre_topc(X3,sK4)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK4)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK5,sK4)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( r1_tsep_1(X3,k1_tsep_1(sK4,sK5,X2))
                & ( ~ r1_tsep_1(X3,X2)
                  | ~ r1_tsep_1(X3,sK5) ) )
              | sP1(X2,X3,sK5,sK4)
              | sP2(X3,X2,sK5,sK4)
              | sP0(X3,X2,sK5,sK4) )
            & m1_pre_topc(X3,sK4)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK4)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( r1_tsep_1(X3,k1_tsep_1(sK4,sK5,sK6))
              & ( ~ r1_tsep_1(X3,sK6)
                | ~ r1_tsep_1(X3,sK5) ) )
            | sP1(sK6,X3,sK5,sK4)
            | sP2(X3,sK6,sK5,sK4)
            | sP0(X3,sK6,sK5,sK4) )
          & m1_pre_topc(X3,sK4)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK6,sK4)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ( ( r1_tsep_1(X3,k1_tsep_1(sK4,sK5,sK6))
            & ( ~ r1_tsep_1(X3,sK6)
              | ~ r1_tsep_1(X3,sK5) ) )
          | sP1(sK6,X3,sK5,sK4)
          | sP2(X3,sK6,sK5,sK4)
          | sP0(X3,sK6,sK5,sK4) )
        & m1_pre_topc(X3,sK4)
        & ~ v2_struct_0(X3) )
   => ( ( ( r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
          & ( ~ r1_tsep_1(sK7,sK6)
            | ~ r1_tsep_1(sK7,sK5) ) )
        | sP1(sK6,sK7,sK5,sK4)
        | sP2(sK7,sK6,sK5,sK4)
        | sP0(sK7,sK6,sK5,sK4) )
      & m1_pre_topc(sK7,sK4)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | sP1(X2,X3,X1,X0)
                    | sP2(X3,X2,X1,X0)
                    | sP0(X3,X2,X1,X0) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f31,f30,f29])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | ( r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1)
                      & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | ( r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3)
                      & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) ) )
                    | ( r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1)
                      & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) ) )
                    | ( r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3)
                      & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                          & ~ ( r1_tsep_1(X3,X2)
                              & r1_tsep_1(X3,X1) ) )
                      & ~ ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1)
                          & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                          & ~ ( r1_tsep_1(X2,X3)
                              & r1_tsep_1(X1,X3) ) )
                      & ~ ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3)
                          & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ~ ( r1_tsep_1(X3,X2)
                            & r1_tsep_1(X3,X1) ) )
                    & ~ ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1)
                        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & ~ ( r1_tsep_1(X2,X3)
                            & r1_tsep_1(X1,X3) ) )
                    & ~ ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3)
                        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tmap_1)).

fof(f150,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f61,f147])).

fof(f61,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f145,plain,(
    ~ spl8_12 ),
    inference(avatar_split_clause,[],[f62,f142])).

fof(f62,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f140,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f63,f137])).

fof(f63,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f135,plain,(
    ~ spl8_10 ),
    inference(avatar_split_clause,[],[f64,f132])).

fof(f64,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f130,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f65,f127])).

fof(f65,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f120,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f67,f117])).

fof(f67,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f115,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f68,f112,f108,f99,f95,f91])).

fof(f68,plain,
    ( ~ r1_tsep_1(sK7,sK6)
    | ~ r1_tsep_1(sK7,sK5)
    | sP1(sK6,sK7,sK5,sK4)
    | sP2(sK7,sK6,sK5,sK4)
    | sP0(sK7,sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f106,plain,
    ( spl8_1
    | spl8_2
    | spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f69,f103,f99,f95,f91])).

fof(f69,plain,
    ( r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | sP1(sK6,sK7,sK5,sK4)
    | sP2(sK7,sK6,sK5,sK4)
    | sP0(sK7,sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

%------------------------------------------------------------------------------
