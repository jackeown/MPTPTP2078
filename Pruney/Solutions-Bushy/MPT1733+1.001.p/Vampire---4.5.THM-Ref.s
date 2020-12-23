%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1733+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:26 EST 2020

% Result     : Theorem 3.08s
% Output     : Refutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 555 expanded)
%              Number of leaves         :   48 ( 258 expanded)
%              Depth                    :   10
%              Number of atoms          :  827 (3067 expanded)
%              Number of equality atoms :   35 (  77 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4683,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f88,f93,f98,f108,f113,f118,f123,f128,f138,f169,f171,f173,f181,f189,f197,f265,f278,f298,f322,f342,f376,f381,f425,f570,f768,f773,f1208,f1281,f4160,f4161,f4303,f4680])).

fof(f4680,plain,
    ( spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | spl6_14
    | ~ spl6_21
    | ~ spl6_25
    | spl6_26
    | ~ spl6_31
    | ~ spl6_42
    | spl6_77
    | ~ spl6_78 ),
    inference(avatar_contradiction_clause,[],[f4679])).

fof(f4679,plain,
    ( $false
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | spl6_14
    | ~ spl6_21
    | ~ spl6_25
    | spl6_26
    | ~ spl6_31
    | ~ spl6_42
    | spl6_77
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f4621,f277])).

fof(f277,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK2,sK3,sK4),sK5)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl6_26
  <=> r1_tsep_1(k2_tsep_1(sK2,sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f4621,plain,
    ( r1_tsep_1(k2_tsep_1(sK2,sK3,sK4),sK5)
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | spl6_14
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_31
    | ~ spl6_42
    | spl6_77
    | ~ spl6_78 ),
    inference(unit_resulting_resolution,[],[f137,f127,f122,f195,f112,f117,f107,f92,f767,f772,f272,f320,f3701,f792])).

fof(f792,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_xboole_0(k3_xboole_0(u1_struct_0(X9),u1_struct_0(X10)),u1_struct_0(X11))
      | r1_tsep_1(k2_tsep_1(X8,X9,X10),X11)
      | ~ l1_struct_0(X11)
      | ~ l1_struct_0(k2_tsep_1(X8,X9,X10))
      | ~ m1_pre_topc(k2_tsep_1(X8,X9,X10),X8)
      | ~ v1_pre_topc(k2_tsep_1(X8,X9,X10))
      | v2_struct_0(k2_tsep_1(X8,X9,X10))
      | r1_tsep_1(X9,X10)
      | ~ m1_pre_topc(X10,X8)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X9,X8)
      | v2_struct_0(X9)
      | ~ l1_pre_topc(X8)
      | v2_struct_0(X8) ) ),
    inference(superposition,[],[f56,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f3701,plain,
    ( ! [X29] : r1_xboole_0(k3_xboole_0(X29,u1_struct_0(sK4)),u1_struct_0(sK5))
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f3693,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f3693,plain,
    ( ! [X29] :
        ( k1_xboole_0 != k3_xboole_0(X29,k1_xboole_0)
        | r1_xboole_0(k3_xboole_0(X29,u1_struct_0(sK4)),u1_struct_0(sK5)) )
    | ~ spl6_42 ),
    inference(superposition,[],[f359,f475])).

fof(f475,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl6_42
  <=> k1_xboole_0 = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f359,plain,(
    ! [X12,X13,X11] :
      ( k1_xboole_0 != k3_xboole_0(X11,k3_xboole_0(X12,X13))
      | r1_xboole_0(k3_xboole_0(X11,X12),X13) ) ),
    inference(superposition,[],[f64,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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

fof(f320,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl6_31
  <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f272,plain,
    ( l1_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl6_25
  <=> l1_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f772,plain,
    ( v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f770])).

fof(f770,plain,
    ( spl6_78
  <=> v1_pre_topc(k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f767,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | spl6_77 ),
    inference(avatar_component_clause,[],[f765])).

fof(f765,plain,
    ( spl6_77
  <=> v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f92,plain,
    ( ~ r1_tsep_1(sK3,sK4)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_5
  <=> r1_tsep_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f107,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_8
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f117,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl6_10
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f112,plain,
    ( ~ v2_struct_0(sK4)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_9
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f195,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl6_21
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f122,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl6_11
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f127,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl6_12
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f137,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_14
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f4303,plain,
    ( spl6_34
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f495,f373,f378])).

fof(f378,plain,
    ( spl6_34
  <=> r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f373,plain,
    ( spl6_33
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f495,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl6_33 ),
    inference(unit_resulting_resolution,[],[f375,f228])).

fof(f228,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_xboole_0(X2,X1) ) ),
    inference(trivial_inequality_removal,[],[f225])).

fof(f225,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X1,X2)
      | ~ r1_xboole_0(X2,X1) ) ),
    inference(superposition,[],[f64,f202])).

fof(f202,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = k3_xboole_0(X4,X3)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f63,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f375,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f373])).

fof(f4161,plain,
    ( ~ spl6_2
    | ~ spl6_1
    | ~ spl6_21
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f2225,f271,f193,f72,f76])).

fof(f76,plain,
    ( spl6_2
  <=> r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f72,plain,
    ( spl6_1
  <=> sP0(sK5,sK4,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f2225,plain,
    ( ~ r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4))
    | ~ spl6_1
    | ~ spl6_21
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f195,f74,f272,f334])).

fof(f334,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X0,k2_tsep_1(X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3)
      | ~ l1_struct_0(k2_tsep_1(X3,X2,X1))
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f41,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_tsep_1(k2_tsep_1(X3,X2,X1),X0)
        & ( r1_tsep_1(X1,X0)
          | r1_tsep_1(X2,X0) ) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
        & ( r1_tsep_1(X2,X3)
          | r1_tsep_1(X1,X3) ) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
        & ( r1_tsep_1(X2,X3)
          | r1_tsep_1(X1,X3) ) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f74,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f4160,plain,
    ( spl6_2
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | spl6_14
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_31
    | ~ spl6_34
    | spl6_77
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f4096,f770,f765,f378,f319,f271,f193,f135,f125,f120,f115,f110,f105,f90,f76])).

fof(f4096,plain,
    ( r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4))
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | spl6_14
    | ~ spl6_21
    | ~ spl6_25
    | ~ spl6_31
    | ~ spl6_34
    | spl6_77
    | ~ spl6_78 ),
    inference(unit_resulting_resolution,[],[f137,f127,f122,f195,f112,f117,f107,f92,f767,f772,f272,f320,f4033,f793])).

fof(f793,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ r1_xboole_0(u1_struct_0(X15),k3_xboole_0(u1_struct_0(X13),u1_struct_0(X14)))
      | r1_tsep_1(X15,k2_tsep_1(X12,X13,X14))
      | ~ l1_struct_0(k2_tsep_1(X12,X13,X14))
      | ~ l1_struct_0(X15)
      | ~ m1_pre_topc(k2_tsep_1(X12,X13,X14),X12)
      | ~ v1_pre_topc(k2_tsep_1(X12,X13,X14))
      | v2_struct_0(k2_tsep_1(X12,X13,X14))
      | r1_tsep_1(X13,X14)
      | ~ m1_pre_topc(X14,X12)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X13,X12)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(X12)
      | v2_struct_0(X12) ) ),
    inference(superposition,[],[f56,f70])).

fof(f4033,plain,
    ( ! [X0] : r1_xboole_0(u1_struct_0(sK5),k3_xboole_0(u1_struct_0(sK3),X0))
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f380,f825])).

fof(f825,plain,(
    ! [X10,X11,X9] :
      ( r1_xboole_0(X9,k3_xboole_0(X10,X11))
      | ~ r1_xboole_0(X9,X10) ) ),
    inference(trivial_inequality_removal,[],[f820])).

fof(f820,plain,(
    ! [X10,X11,X9] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X9,k3_xboole_0(X10,X11))
      | ~ r1_xboole_0(X9,X10) ) ),
    inference(superposition,[],[f64,f364])).

fof(f364,plain,(
    ! [X6,X7,X5] :
      ( k1_xboole_0 = k3_xboole_0(X5,k3_xboole_0(X6,X7))
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(forward_demodulation,[],[f345,f198])).

fof(f198,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f61,f54])).

fof(f345,plain,(
    ! [X6,X7,X5] :
      ( k3_xboole_0(k1_xboole_0,X7) = k3_xboole_0(X5,k3_xboole_0(X6,X7))
      | ~ r1_xboole_0(X5,X6) ) ),
    inference(superposition,[],[f65,f63])).

fof(f380,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f378])).

fof(f1281,plain,
    ( spl6_42
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f1273,f448,f474])).

fof(f448,plain,
    ( spl6_38
  <=> r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f1273,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f449,f202])).

fof(f449,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f448])).

fof(f1208,plain,
    ( ~ spl6_4
    | ~ spl6_20
    | ~ spl6_21
    | spl6_38 ),
    inference(avatar_split_clause,[],[f462,f448,f193,f185,f85])).

fof(f85,plain,
    ( spl6_4
  <=> r1_tsep_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f185,plain,
    ( spl6_20
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f462,plain,
    ( ~ r1_tsep_1(sK5,sK4)
    | ~ spl6_20
    | ~ spl6_21
    | spl6_38 ),
    inference(unit_resulting_resolution,[],[f195,f187,f450,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f450,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | spl6_38 ),
    inference(avatar_component_clause,[],[f448])).

fof(f187,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f773,plain,
    ( spl6_78
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f762,f338,f770])).

fof(f338,plain,
    ( spl6_32
  <=> sP1(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f762,plain,
    ( v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f339,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k2_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k2_tsep_1(X0,X2,X1)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f339,plain,
    ( sP1(sK2,sK4,sK3)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f338])).

fof(f768,plain,
    ( ~ spl6_77
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f763,f338,f765])).

fof(f763,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f339,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f570,plain,
    ( spl6_32
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | spl6_14 ),
    inference(avatar_split_clause,[],[f536,f135,f125,f120,f115,f110,f105,f338])).

fof(f536,plain,
    ( sP1(sK2,sK4,sK3)
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f137,f127,f122,f117,f112,f107,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f26])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
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
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f425,plain,
    ( spl6_24
    | ~ spl6_1
    | spl6_23 ),
    inference(avatar_split_clause,[],[f411,f254,f72,f259])).

fof(f259,plain,
    ( spl6_24
  <=> r1_tsep_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f254,plain,
    ( spl6_23
  <=> r1_tsep_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f411,plain,
    ( r1_tsep_1(sK3,sK5)
    | ~ spl6_1
    | spl6_23 ),
    inference(unit_resulting_resolution,[],[f256,f74,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X2,X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f256,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f254])).

fof(f381,plain,
    ( spl6_34
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f370,f193,f177,f81,f378])).

fof(f81,plain,
    ( spl6_3
  <=> r1_tsep_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f177,plain,
    ( spl6_19
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f370,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f195,f179,f83,f55])).

fof(f83,plain,
    ( r1_tsep_1(sK5,sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f179,plain,
    ( l1_struct_0(sK3)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f177])).

fof(f376,plain,
    ( spl6_33
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f371,f259,f193,f177,f373])).

fof(f371,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f179,f195,f261,f55])).

fof(f261,plain,
    ( r1_tsep_1(sK3,sK5)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f259])).

fof(f342,plain,
    ( ~ spl6_32
    | spl6_31 ),
    inference(avatar_split_clause,[],[f336,f319,f338])).

fof(f336,plain,
    ( ~ sP1(sK2,sK4,sK3)
    | spl6_31 ),
    inference(resolution,[],[f321,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f321,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f319])).

fof(f322,plain,
    ( ~ spl6_31
    | ~ spl6_12
    | spl6_27 ),
    inference(avatar_split_clause,[],[f299,f295,f125,f319])).

fof(f295,plain,
    ( spl6_27
  <=> l1_pre_topc(k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f299,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | ~ spl6_12
    | spl6_27 ),
    inference(unit_resulting_resolution,[],[f127,f297,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f297,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f295])).

fof(f298,plain,
    ( ~ spl6_27
    | spl6_25 ),
    inference(avatar_split_clause,[],[f293,f271,f295])).

fof(f293,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | spl6_25 ),
    inference(unit_resulting_resolution,[],[f273,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f273,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f271])).

fof(f278,plain,
    ( ~ spl6_25
    | ~ spl6_26
    | spl6_2
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f269,f193,f76,f275,f271])).

fof(f269,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK2,sK3,sK4),sK5)
    | ~ l1_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | spl6_2
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f247,f195])).

fof(f247,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK2,sK3,sK4),sK5)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | spl6_2 ),
    inference(resolution,[],[f62,f78])).

fof(f78,plain,
    ( ~ r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f265,plain,
    ( ~ spl6_23
    | spl6_4
    | ~ spl6_20
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f264,f193,f185,f85,f254])).

fof(f264,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | spl6_4
    | ~ spl6_20
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f263,f187])).

fof(f263,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK4)
    | spl6_4
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f245,f195])).

fof(f245,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4)
    | spl6_4 ),
    inference(resolution,[],[f62,f86])).

fof(f86,plain,
    ( ~ r1_tsep_1(sK5,sK4)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f197,plain,
    ( spl6_21
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f191,f164,f193])).

fof(f164,plain,
    ( spl6_18
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f191,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_18 ),
    inference(resolution,[],[f166,f57])).

fof(f166,plain,
    ( l1_pre_topc(sK5)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f189,plain,
    ( spl6_20
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f183,f159,f185])).

fof(f159,plain,
    ( spl6_17
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f183,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_17 ),
    inference(resolution,[],[f161,f57])).

fof(f161,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f181,plain,
    ( spl6_19
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f175,f154,f177])).

fof(f154,plain,
    ( spl6_16
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f175,plain,
    ( l1_struct_0(sK3)
    | ~ spl6_16 ),
    inference(resolution,[],[f156,f57])).

fof(f156,plain,
    ( l1_pre_topc(sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f154])).

fof(f173,plain,
    ( spl6_16
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f172,f125,f115,f154])).

fof(f172,plain,
    ( l1_pre_topc(sK3)
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f152,f127])).

fof(f152,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f58,f117])).

fof(f171,plain,
    ( spl6_17
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f170,f125,f105,f159])).

fof(f170,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f151,f127])).

fof(f151,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f58,f107])).

fof(f169,plain,
    ( spl6_18
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f168,f125,f95,f164])).

fof(f95,plain,
    ( spl6_6
  <=> m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f168,plain,
    ( l1_pre_topc(sK5)
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f150,f127])).

fof(f150,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f58,f97])).

fof(f97,plain,
    ( m1_pre_topc(sK5,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f138,plain,(
    ~ spl6_14 ),
    inference(avatar_split_clause,[],[f42,f135])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ( ~ r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4))
        & ( r1_tsep_1(sK5,sK4)
          | r1_tsep_1(sK5,sK3) ) )
      | sP0(sK5,sK4,sK3,sK2) )
    & ~ r1_tsep_1(sK3,sK4)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f25,f33,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                        & ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) ) )
                      | sP0(X3,X2,X1,X0) )
                    & ~ r1_tsep_1(X1,X2)
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
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK2,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | sP0(X3,X2,X1,sK2) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK2,X1,X2))
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X3,X1) ) )
                  | sP0(X3,X2,X1,sK2) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK2,sK3,X2))
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X3,sK3) ) )
                | sP0(X3,X2,sK3,sK2) )
              & ~ r1_tsep_1(sK3,X2)
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK2,sK3,X2))
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X3,sK3) ) )
              | sP0(X3,X2,sK3,sK2) )
            & ~ r1_tsep_1(sK3,X2)
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK2,sK3,sK4))
              & ( r1_tsep_1(X3,sK4)
                | r1_tsep_1(X3,sK3) ) )
            | sP0(X3,sK4,sK3,sK2) )
          & ~ r1_tsep_1(sK3,sK4)
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK2,sK3,sK4))
            & ( r1_tsep_1(X3,sK4)
              | r1_tsep_1(X3,sK3) ) )
          | sP0(X3,sK4,sK3,sK2) )
        & ~ r1_tsep_1(sK3,sK4)
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ( ( ~ r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4))
          & ( r1_tsep_1(sK5,sK4)
            | r1_tsep_1(sK5,sK3) ) )
        | sP0(sK5,sK4,sK3,sK2) )
      & ~ r1_tsep_1(sK3,sK4)
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | sP0(X3,X2,X1,X0) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f24])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( ( r1_tsep_1(X3,X2)
                            | r1_tsep_1(X3,X1) )
                         => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                        & ( ( r1_tsep_1(X2,X3)
                            | r1_tsep_1(X1,X3) )
                         => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                      & ( ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tmap_1)).

fof(f128,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f44,f125])).

fof(f44,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f123,plain,(
    ~ spl6_11 ),
    inference(avatar_split_clause,[],[f45,f120])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f118,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f46,f115])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f113,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f47,f110])).

fof(f47,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f108,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f48,f105])).

fof(f48,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f98,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f50,f95])).

fof(f50,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f93,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f51,f90])).

fof(f51,plain,(
    ~ r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,
    ( spl6_1
    | spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f52,f85,f81,f72])).

fof(f52,plain,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK5,sK3)
    | sP0(sK5,sK4,sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f53,f76,f72])).

fof(f53,plain,
    ( ~ r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4))
    | sP0(sK5,sK4,sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

%------------------------------------------------------------------------------
