%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1731+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:26 EST 2020

% Result     : Theorem 2.78s
% Output     : Refutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  327 ( 918 expanded)
%              Number of leaves         :   66 ( 430 expanded)
%              Depth                    :   10
%              Number of atoms          : 1113 (4024 expanded)
%              Number of equality atoms :   69 ( 222 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4495,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f115,f120,f130,f135,f140,f145,f150,f160,f165,f179,f185,f211,f213,f215,f221,f227,f233,f253,f255,f257,f322,f327,f332,f337,f348,f382,f477,f583,f588,f593,f598,f753,f839,f843,f849,f876,f1162,f1168,f3465,f3467,f3469,f3472,f3473,f4094,f4102,f4113,f4121,f4124,f4126,f4131,f4172,f4177,f4180,f4469,f4471,f4475,f4484,f4487,f4489])).

fof(f4489,plain,
    ( ~ spl8_30
    | ~ spl8_32
    | spl8_138 ),
    inference(avatar_split_clause,[],[f4488,f1165,f345,f329])).

fof(f329,plain,
    ( spl8_30
  <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f345,plain,
    ( spl8_32
  <=> k1_xboole_0 = k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f1165,plain,
    ( spl8_138
  <=> r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).

fof(f4488,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_138 ),
    inference(forward_demodulation,[],[f4443,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f4443,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_138 ),
    inference(resolution,[],[f785,f1166])).

fof(f1166,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))
    | spl8_138 ),
    inference(avatar_component_clause,[],[f1165])).

fof(f785,plain,(
    ! [X14,X12,X13] :
      ( r1_xboole_0(X12,k2_xboole_0(X13,X14))
      | k1_xboole_0 != k3_xboole_0(X12,X13)
      | ~ r1_xboole_0(X12,X14) ) ),
    inference(superposition,[],[f83,f366])).

fof(f366,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X3,X5) = k3_xboole_0(X3,k2_xboole_0(X5,X4))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(forward_demodulation,[],[f359,f71])).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f359,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f84,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f4487,plain,
    ( spl8_32
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f4228,f334,f345])).

fof(f334,plain,
    ( spl8_31
  <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f4228,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | ~ spl8_31 ),
    inference(unit_resulting_resolution,[],[f335,f263])).

fof(f263,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k3_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f82,f79])).

fof(f335,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f334])).

fof(f4484,plain,
    ( ~ spl8_1
    | spl8_92 ),
    inference(avatar_split_clause,[],[f4241,f831,f91])).

fof(f91,plain,
    ( spl8_1
  <=> sP2(sK7,sK6,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f831,plain,
    ( spl8_92
  <=> r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f4241,plain,
    ( ~ sP2(sK7,sK6,sK5,sK4)
    | spl8_92 ),
    inference(unit_resulting_resolution,[],[f832,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ~ r1_tsep_1(X1,X0)
          | ~ r1_tsep_1(X2,X0) )
        & r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( ~ r1_tsep_1(X2,X3)
          | ~ r1_tsep_1(X1,X3) )
        & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( ~ r1_tsep_1(X2,X3)
          | ~ r1_tsep_1(X1,X3) )
        & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f832,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7)
    | spl8_92 ),
    inference(avatar_component_clause,[],[f831])).

fof(f4475,plain,
    ( spl8_35
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f3500,f319,f379])).

fof(f379,plain,
    ( spl8_35
  <=> k1_xboole_0 = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f319,plain,
    ( spl8_28
  <=> r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f3500,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f320,f82])).

fof(f320,plain,
    ( r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f319])).

fof(f4471,plain,
    ( spl8_30
    | ~ spl8_4
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f3477,f230,f224,f103,f329])).

fof(f103,plain,
    ( spl8_4
  <=> r1_tsep_1(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f224,plain,
    ( spl8_24
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f230,plain,
    ( spl8_25
  <=> l1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f3477,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ spl8_4
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f232,f226,f104,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f104,plain,
    ( r1_tsep_1(sK7,sK6)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f226,plain,
    ( l1_struct_0(sK6)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f224])).

fof(f232,plain,
    ( l1_struct_0(sK7)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f230])).

fof(f4469,plain,
    ( ~ spl8_30
    | ~ spl8_33
    | spl8_138 ),
    inference(avatar_split_clause,[],[f4438,f1165,f350,f329])).

fof(f350,plain,
    ( spl8_33
  <=> k1_xboole_0 = k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f4438,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ spl8_33
    | spl8_138 ),
    inference(unit_resulting_resolution,[],[f1166,f351,f785])).

fof(f351,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f350])).

fof(f4180,plain,
    ( spl8_6
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15
    | ~ spl8_25
    | spl8_59
    | ~ spl8_60
    | ~ spl8_61
    | ~ spl8_86
    | ~ spl8_138 ),
    inference(avatar_split_clause,[],[f3202,f1165,f750,f590,f585,f580,f230,f157,f147,f142,f137,f132,f127,f112])).

fof(f112,plain,
    ( spl8_6
  <=> r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

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

fof(f580,plain,
    ( spl8_59
  <=> v2_struct_0(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f585,plain,
    ( spl8_60
  <=> v1_pre_topc(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f590,plain,
    ( spl8_61
  <=> m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f750,plain,
    ( spl8_86
  <=> l1_struct_0(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f3202,plain,
    ( r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15
    | ~ spl8_25
    | spl8_59
    | ~ spl8_60
    | ~ spl8_61
    | ~ spl8_86
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f159,f149,f144,f232,f134,f139,f129,f582,f587,f752,f592,f1167,f728])).

fof(f728,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1167,plain,
    ( r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))
    | ~ spl8_138 ),
    inference(avatar_component_clause,[],[f1165])).

fof(f592,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4)
    | ~ spl8_61 ),
    inference(avatar_component_clause,[],[f590])).

fof(f752,plain,
    ( l1_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_86 ),
    inference(avatar_component_clause,[],[f750])).

fof(f587,plain,
    ( v1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f585])).

fof(f582,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | spl8_59 ),
    inference(avatar_component_clause,[],[f580])).

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

fof(f4177,plain,
    ( ~ spl8_2
    | ~ spl8_6
    | ~ spl8_25
    | ~ spl8_86 ),
    inference(avatar_split_clause,[],[f2565,f750,f230,f112,f95])).

fof(f95,plain,
    ( spl8_2
  <=> sP0(sK7,sK6,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f2565,plain,
    ( ~ sP0(sK7,sK6,sK5,sK4)
    | ~ spl8_6
    | ~ spl8_25
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f232,f752,f114,f310])).

fof(f310,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tsep_1(X4,k1_tsep_1(X7,X6,X5))
      | ~ sP0(X4,X5,X6,X7)
      | ~ l1_struct_0(k1_tsep_1(X7,X6,X5))
      | ~ l1_struct_0(X4) ) ),
    inference(resolution,[],[f58,f81])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
        & r1_tsep_1(X1,X0)
        & r1_tsep_1(X2,X0) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
        & r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
        & r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f114,plain,
    ( r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f4172,plain,
    ( spl8_32
    | ~ spl8_500
    | ~ spl8_501 ),
    inference(avatar_split_clause,[],[f4171,f4099,f4091,f345])).

fof(f4091,plain,
    ( spl8_500
  <=> k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_500])])).

fof(f4099,plain,
    ( spl8_501
  <=> k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_501])])).

fof(f4171,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | ~ spl8_500
    | ~ spl8_501 ),
    inference(backward_demodulation,[],[f4101,f4093])).

fof(f4093,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(sK7)))
    | ~ spl8_500 ),
    inference(avatar_component_clause,[],[f4091])).

fof(f4101,plain,
    ( k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(sK7)))
    | ~ spl8_501 ),
    inference(avatar_component_clause,[],[f4099])).

fof(f4131,plain,
    ( ~ spl8_32
    | spl8_31 ),
    inference(avatar_split_clause,[],[f384,f334,f345])).

fof(f384,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | spl8_31 ),
    inference(unit_resulting_resolution,[],[f336,f268])).

fof(f268,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k3_xboole_0(X3,X2)
      | r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f83,f79])).

fof(f336,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | spl8_31 ),
    inference(avatar_component_clause,[],[f334])).

fof(f4126,plain,
    ( ~ spl8_29
    | spl8_33 ),
    inference(avatar_split_clause,[],[f416,f350,f324])).

fof(f324,plain,
    ( spl8_29
  <=> r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f416,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | spl8_33 ),
    inference(unit_resulting_resolution,[],[f352,f263])).

fof(f352,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | spl8_33 ),
    inference(avatar_component_clause,[],[f350])).

fof(f4124,plain,
    ( ~ spl8_26
    | ~ spl8_1
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f4123,f287,f91,f249])).

fof(f249,plain,
    ( spl8_26
  <=> r1_tsep_1(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f287,plain,
    ( spl8_27
  <=> r1_tsep_1(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f4123,plain,
    ( ~ r1_tsep_1(sK5,sK7)
    | ~ spl8_1
    | ~ spl8_27 ),
    inference(subsumption_resolution,[],[f860,f289])).

fof(f289,plain,
    ( r1_tsep_1(sK6,sK7)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f287])).

fof(f860,plain,
    ( ~ r1_tsep_1(sK5,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ spl8_1 ),
    inference(resolution,[],[f93,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ r1_tsep_1(X2,X0)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,
    ( sP2(sK7,sK6,sK5,sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f4121,plain,
    ( ~ spl8_3
    | ~ spl8_23
    | ~ spl8_25
    | spl8_31 ),
    inference(avatar_split_clause,[],[f383,f334,f230,f218,f99])).

fof(f99,plain,
    ( spl8_3
  <=> r1_tsep_1(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f218,plain,
    ( spl8_23
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f383,plain,
    ( ~ r1_tsep_1(sK7,sK5)
    | ~ spl8_23
    | ~ spl8_25
    | spl8_31 ),
    inference(unit_resulting_resolution,[],[f232,f220,f336,f72])).

fof(f220,plain,
    ( l1_struct_0(sK5)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f218])).

fof(f4113,plain,
    ( ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f882,f112,f107])).

fof(f107,plain,
    ( spl8_5
  <=> sP1(sK6,sK5,sK4,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f882,plain,
    ( ~ sP1(sK6,sK5,sK4,sK7)
    | ~ spl8_6 ),
    inference(resolution,[],[f114,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0))
        & r1_tsep_1(X3,X0)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X2,X1,X0,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
        & r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
        & r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f4102,plain,
    ( spl8_501
    | ~ spl8_30
    | ~ spl8_138 ),
    inference(avatar_split_clause,[],[f4097,f1165,f329,f4099])).

fof(f4097,plain,
    ( k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(sK7)))
    | ~ spl8_30
    | ~ spl8_138 ),
    inference(forward_demodulation,[],[f4096,f79])).

fof(f4096,plain,
    ( k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(sK7)))
    | ~ spl8_30
    | ~ spl8_138 ),
    inference(forward_demodulation,[],[f4095,f3490])).

fof(f3490,plain,
    ( ! [X0] : k3_xboole_0(u1_struct_0(sK7),X0) = k3_xboole_0(u1_struct_0(sK7),k2_xboole_0(X0,u1_struct_0(sK6)))
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f330,f366])).

fof(f330,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f329])).

fof(f4095,plain,
    ( k3_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(sK7)))
    | ~ spl8_138 ),
    inference(forward_demodulation,[],[f4014,f79])).

fof(f4014,plain,
    ( k3_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))) = k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0(sK7),k1_xboole_0))
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f1167,f2017])).

fof(f2017,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,k1_xboole_0))
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(superposition,[],[f355,f71])).

fof(f355,plain,(
    ! [X4,X5,X3] :
      ( k3_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X3,X5))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f84,f82])).

fof(f4094,plain,
    ( spl8_500
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f4089,f379,f329,f4091])).

fof(f4089,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(sK7)))
    | ~ spl8_30
    | ~ spl8_35 ),
    inference(forward_demodulation,[],[f4088,f380])).

fof(f380,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f379])).

fof(f4088,plain,
    ( k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(sK7)))
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f4087,f79])).

fof(f4087,plain,
    ( k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,u1_struct_0(sK7)))
    | ~ spl8_30 ),
    inference(forward_demodulation,[],[f4015,f79])).

fof(f4015,plain,
    ( k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(u1_struct_0(sK7),k1_xboole_0))
    | ~ spl8_30 ),
    inference(unit_resulting_resolution,[],[f330,f2017])).

fof(f3473,plain,
    ( ~ spl8_37
    | spl8_35 ),
    inference(avatar_split_clause,[],[f3193,f379,f441])).

fof(f441,plain,
    ( spl8_37
  <=> v1_xboole_0(k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f3193,plain,
    ( ~ v1_xboole_0(k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)))
    | spl8_35 ),
    inference(unit_resulting_resolution,[],[f381,f74])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f381,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | spl8_35 ),
    inference(avatar_component_clause,[],[f379])).

fof(f3472,plain,
    ( spl8_37
    | ~ spl8_19
    | ~ spl8_138 ),
    inference(avatar_split_clause,[],[f3456,f1165,f182,f441])).

fof(f182,plain,
    ( spl8_19
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f3456,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7)))
    | ~ spl8_19
    | ~ spl8_138 ),
    inference(forward_demodulation,[],[f3446,f79])).

fof(f3446,plain,
    ( v1_xboole_0(k3_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)))
    | ~ spl8_19
    | ~ spl8_138 ),
    inference(unit_resulting_resolution,[],[f1167,f763])).

fof(f763,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_xboole_0(X3,k2_xboole_0(X4,X5))
        | v1_xboole_0(k3_xboole_0(X3,X5)) )
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f759,f184])).

fof(f184,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f759,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | v1_xboole_0(k3_xboole_0(X3,X5))
      | ~ r1_xboole_0(X3,k2_xboole_0(X4,X5)) ) ),
    inference(superposition,[],[f364,f82])).

fof(f364,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_xboole_0)).

fof(f3469,plain,
    ( ~ spl8_30
    | spl8_28 ),
    inference(avatar_split_clause,[],[f391,f319,f329])).

fof(f391,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_28 ),
    inference(unit_resulting_resolution,[],[f321,f275])).

fof(f275,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(superposition,[],[f83,f263])).

fof(f321,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | spl8_28 ),
    inference(avatar_component_clause,[],[f319])).

fof(f3467,plain,
    ( ~ spl8_30
    | spl8_35 ),
    inference(avatar_split_clause,[],[f3195,f379,f329])).

fof(f3195,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_35 ),
    inference(unit_resulting_resolution,[],[f381,f263])).

fof(f3465,plain,
    ( ~ spl8_27
    | ~ spl8_24
    | ~ spl8_25
    | spl8_28 ),
    inference(avatar_split_clause,[],[f389,f319,f230,f224,f287])).

fof(f389,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | ~ spl8_24
    | ~ spl8_25
    | spl8_28 ),
    inference(unit_resulting_resolution,[],[f226,f232,f321,f72])).

fof(f1168,plain,
    ( spl8_138
    | ~ spl8_93
    | ~ spl8_137 ),
    inference(avatar_split_clause,[],[f1163,f1159,f836,f1165])).

fof(f836,plain,
    ( spl8_93
  <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_93])])).

fof(f1159,plain,
    ( spl8_137
  <=> u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) = k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).

fof(f1163,plain,
    ( r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))
    | ~ spl8_93
    | ~ spl8_137 ),
    inference(backward_demodulation,[],[f838,f1161])).

fof(f1161,plain,
    ( u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) = k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ spl8_137 ),
    inference(avatar_component_clause,[],[f1159])).

fof(f838,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | ~ spl8_93 ),
    inference(avatar_component_clause,[],[f836])).

fof(f1162,plain,
    ( spl8_137
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15
    | spl8_59
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(avatar_split_clause,[],[f1075,f590,f585,f580,f157,f147,f142,f137,f132,f127,f1159])).

fof(f1075,plain,
    ( u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) = k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15
    | spl8_59
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(unit_resulting_resolution,[],[f159,f149,f144,f134,f139,f129,f582,f587,f592,f89])).

fof(f876,plain,
    ( spl8_6
    | ~ spl8_25
    | ~ spl8_86
    | ~ spl8_92 ),
    inference(avatar_contradiction_clause,[],[f875])).

fof(f875,plain,
    ( $false
    | spl8_6
    | ~ spl8_25
    | ~ spl8_86
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f874,f752])).

fof(f874,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | spl8_6
    | ~ spl8_25
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f873,f232])).

fof(f873,plain,
    ( ~ l1_struct_0(sK7)
    | ~ l1_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | spl8_6
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f870,f833])).

fof(f833,plain,
    ( r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7)
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f831])).

fof(f870,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7)
    | ~ l1_struct_0(sK7)
    | ~ l1_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | spl8_6 ),
    inference(resolution,[],[f113,f81])).

fof(f113,plain,
    ( ~ r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f849,plain,
    ( ~ spl8_2
    | spl8_27 ),
    inference(avatar_contradiction_clause,[],[f848])).

fof(f848,plain,
    ( $false
    | ~ spl8_2
    | spl8_27 ),
    inference(subsumption_resolution,[],[f97,f298])).

fof(f298,plain,
    ( ! [X0,X1] : ~ sP0(sK7,sK6,X0,X1)
    | spl8_27 ),
    inference(unit_resulting_resolution,[],[f288,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f288,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | spl8_27 ),
    inference(avatar_component_clause,[],[f287])).

fof(f97,plain,
    ( sP0(sK7,sK6,sK5,sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f843,plain,
    ( ~ spl8_26
    | ~ spl8_23
    | ~ spl8_25
    | spl8_29 ),
    inference(avatar_split_clause,[],[f338,f324,f230,f218,f249])).

fof(f338,plain,
    ( ~ r1_tsep_1(sK5,sK7)
    | ~ spl8_23
    | ~ spl8_25
    | spl8_29 ),
    inference(unit_resulting_resolution,[],[f220,f232,f326,f72])).

fof(f326,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | spl8_29 ),
    inference(avatar_component_clause,[],[f324])).

fof(f839,plain,
    ( spl8_93
    | ~ spl8_6
    | ~ spl8_25
    | ~ spl8_86 ),
    inference(avatar_split_clause,[],[f828,f750,f230,f112,f836])).

fof(f828,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | ~ spl8_6
    | ~ spl8_25
    | ~ spl8_86 ),
    inference(unit_resulting_resolution,[],[f232,f114,f752,f72])).

fof(f753,plain,
    ( spl8_86
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f748,f595,f750])).

fof(f595,plain,
    ( spl8_62
  <=> l1_pre_topc(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f748,plain,
    ( l1_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_62 ),
    inference(unit_resulting_resolution,[],[f597,f75])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f597,plain,
    ( l1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f595])).

fof(f598,plain,
    ( spl8_62
    | ~ spl8_13
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f575,f474,f147,f595])).

fof(f474,plain,
    ( spl8_41
  <=> sP3(sK4,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f575,plain,
    ( l1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_13
    | ~ spl8_41 ),
    inference(unit_resulting_resolution,[],[f149,f476,f303])).

fof(f303,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP3(X0,X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f87,f76])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
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

fof(f476,plain,
    ( sP3(sK4,sK6,sK5)
    | ~ spl8_41 ),
    inference(avatar_component_clause,[],[f474])).

fof(f593,plain,
    ( spl8_61
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f576,f474,f590])).

fof(f576,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4)
    | ~ spl8_41 ),
    inference(unit_resulting_resolution,[],[f476,f87])).

fof(f588,plain,
    ( spl8_60
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f577,f474,f585])).

fof(f577,plain,
    ( v1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_41 ),
    inference(unit_resulting_resolution,[],[f476,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f583,plain,
    ( ~ spl8_59
    | ~ spl8_41 ),
    inference(avatar_split_clause,[],[f578,f474,f580])).

fof(f578,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_41 ),
    inference(unit_resulting_resolution,[],[f476,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f477,plain,
    ( spl8_41
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(avatar_split_clause,[],[f454,f157,f147,f142,f137,f132,f127,f474])).

fof(f454,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f382,plain,
    ( ~ spl8_35
    | spl8_30 ),
    inference(avatar_split_clause,[],[f368,f329,f379])).

fof(f368,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | spl8_30 ),
    inference(unit_resulting_resolution,[],[f331,f268])).

fof(f331,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_30 ),
    inference(avatar_component_clause,[],[f329])).

fof(f348,plain,
    ( ~ spl8_32
    | spl8_29 ),
    inference(avatar_split_clause,[],[f341,f324,f345])).

fof(f341,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | spl8_29 ),
    inference(unit_resulting_resolution,[],[f326,f83])).

fof(f337,plain,
    ( ~ spl8_31
    | spl8_3
    | ~ spl8_23
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f311,f230,f218,f99,f334])).

fof(f311,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | spl8_3
    | ~ spl8_23
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f232,f220,f101,f73])).

fof(f101,plain,
    ( ~ r1_tsep_1(sK7,sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f332,plain,
    ( ~ spl8_30
    | spl8_4
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f312,f230,f224,f103,f329])).

fof(f312,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_4
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(unit_resulting_resolution,[],[f232,f226,f105,f73])).

fof(f105,plain,
    ( ~ r1_tsep_1(sK7,sK6)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f327,plain,
    ( ~ spl8_29
    | ~ spl8_23
    | ~ spl8_25
    | spl8_26 ),
    inference(avatar_split_clause,[],[f313,f249,f230,f218,f324])).

fof(f313,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK7))
    | ~ spl8_23
    | ~ spl8_25
    | spl8_26 ),
    inference(unit_resulting_resolution,[],[f220,f232,f250,f73])).

fof(f250,plain,
    ( ~ r1_tsep_1(sK5,sK7)
    | spl8_26 ),
    inference(avatar_component_clause,[],[f249])).

fof(f322,plain,
    ( ~ spl8_28
    | ~ spl8_24
    | ~ spl8_25
    | spl8_27 ),
    inference(avatar_split_clause,[],[f314,f287,f230,f224,f319])).

fof(f314,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK6),u1_struct_0(sK7))
    | ~ spl8_24
    | ~ spl8_25
    | spl8_27 ),
    inference(unit_resulting_resolution,[],[f226,f232,f288,f73])).

fof(f257,plain,
    ( spl8_3
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f109,f237])).

fof(f237,plain,
    ( ! [X0,X1] : ~ sP1(X0,sK5,X1,sK7)
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f101,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_tsep_1(X3,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f109,plain,
    ( sP1(sK6,sK5,sK4,sK7)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f255,plain,
    ( spl8_4
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f109,f241])).

fof(f241,plain,
    ( ! [X0,X1] : ~ sP1(sK6,X0,X1,sK7)
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f105,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_tsep_1(X3,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f253,plain,
    ( spl8_26
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f247,f95,f249])).

fof(f247,plain,
    ( r1_tsep_1(sK5,sK7)
    | ~ spl8_2 ),
    inference(resolution,[],[f56,f97])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f160,plain,(
    ~ spl8_15 ),
    inference(avatar_split_clause,[],[f59,f157])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( sP1(sK6,sK5,sK4,sK7)
      | ( ( ~ r1_tsep_1(sK7,sK6)
          | ~ r1_tsep_1(sK7,sK5) )
        & r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6)) )
      | sP0(sK7,sK6,sK5,sK4)
      | sP2(sK7,sK6,sK5,sK4) )
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
                    ( ( sP1(X2,X1,X0,X3)
                      | ( ( ~ r1_tsep_1(X3,X2)
                          | ~ r1_tsep_1(X3,X1) )
                        & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      | sP0(X3,X2,X1,X0)
                      | sP2(X3,X2,X1,X0) )
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
                  ( ( sP1(X2,X1,sK4,X3)
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(sK4,X1,X2)) )
                    | sP0(X3,X2,X1,sK4)
                    | sP2(X3,X2,X1,sK4) )
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
                ( ( sP1(X2,X1,sK4,X3)
                  | ( ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1) )
                    & r1_tsep_1(X3,k1_tsep_1(sK4,X1,X2)) )
                  | sP0(X3,X2,X1,sK4)
                  | sP2(X3,X2,X1,sK4) )
                & m1_pre_topc(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK4)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK4)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( sP1(X2,sK5,sK4,X3)
                | ( ( ~ r1_tsep_1(X3,X2)
                    | ~ r1_tsep_1(X3,sK5) )
                  & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,X2)) )
                | sP0(X3,X2,sK5,sK4)
                | sP2(X3,X2,sK5,sK4) )
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
            ( ( sP1(X2,sK5,sK4,X3)
              | ( ( ~ r1_tsep_1(X3,X2)
                  | ~ r1_tsep_1(X3,sK5) )
                & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,X2)) )
              | sP0(X3,X2,sK5,sK4)
              | sP2(X3,X2,sK5,sK4) )
            & m1_pre_topc(X3,sK4)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK4)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( sP1(sK6,sK5,sK4,X3)
            | ( ( ~ r1_tsep_1(X3,sK6)
                | ~ r1_tsep_1(X3,sK5) )
              & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,sK6)) )
            | sP0(X3,sK6,sK5,sK4)
            | sP2(X3,sK6,sK5,sK4) )
          & m1_pre_topc(X3,sK4)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK6,sK4)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X3] :
        ( ( sP1(sK6,sK5,sK4,X3)
          | ( ( ~ r1_tsep_1(X3,sK6)
              | ~ r1_tsep_1(X3,sK5) )
            & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,sK6)) )
          | sP0(X3,sK6,sK5,sK4)
          | sP2(X3,sK6,sK5,sK4) )
        & m1_pre_topc(X3,sK4)
        & ~ v2_struct_0(X3) )
   => ( ( sP1(sK6,sK5,sK4,sK7)
        | ( ( ~ r1_tsep_1(sK7,sK6)
            | ~ r1_tsep_1(sK7,sK5) )
          & r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6)) )
        | sP0(sK7,sK6,sK5,sK4)
        | sP2(sK7,sK6,sK5,sK4) )
      & m1_pre_topc(sK7,sK4)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( sP1(X2,X1,X0,X3)
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | sP0(X3,X2,X1,X0)
                    | sP2(X3,X2,X1,X0) )
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
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
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
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
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
                   => ( ( ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                       => ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) ) )
                      & ( ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                      & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                       => ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
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
                 => ( ( ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) )
                     => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                     => ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) )
                     => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                    & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                     => ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tmap_1)).

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
    | spl8_6
    | spl8_5 ),
    inference(avatar_split_clause,[],[f68,f107,f112,f95,f91])).

fof(f68,plain,
    ( sP1(sK6,sK5,sK4,sK7)
    | r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | sP0(sK7,sK6,sK5,sK4)
    | sP2(sK7,sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f110,plain,
    ( spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f69,f107,f103,f99,f95,f91])).

fof(f69,plain,
    ( sP1(sK6,sK5,sK4,sK7)
    | ~ r1_tsep_1(sK7,sK6)
    | ~ r1_tsep_1(sK7,sK5)
    | sP0(sK7,sK6,sK5,sK4)
    | sP2(sK7,sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

%------------------------------------------------------------------------------
