%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1723+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:25 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :  263 ( 774 expanded)
%              Number of leaves         :   63 ( 384 expanded)
%              Depth                    :    9
%              Number of atoms          : 1026 (3883 expanded)
%              Number of equality atoms :   25 (  64 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2065,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f160,f166,f193,f195,f201,f208,f272,f319,f478,f493,f498,f570,f575,f580,f624,f629,f634,f644,f670,f688,f693,f698,f1168,f1169,f1315,f1679,f1689,f1693,f1706,f1750,f2048,f2059,f2063])).

fof(f2063,plain,
    ( ~ spl7_138
    | spl7_257
    | ~ spl7_259 ),
    inference(avatar_contradiction_clause,[],[f2062])).

fof(f2062,plain,
    ( $false
    | ~ spl7_138
    | spl7_257
    | ~ spl7_259 ),
    inference(subsumption_resolution,[],[f2061,f1874])).

fof(f1874,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(u1_struct_0(sK4),X0),k3_xboole_0(X0,u1_struct_0(sK6)))
    | ~ spl7_138 ),
    inference(unit_resulting_resolution,[],[f1183,f233])).

fof(f233,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X2,X1),k3_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f79,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f1183,plain,
    ( r1_tarski(u1_struct_0(sK4),u1_struct_0(sK6))
    | ~ spl7_138 ),
    inference(avatar_component_clause,[],[f1182])).

fof(f1182,plain,
    ( spl7_138
  <=> r1_tarski(u1_struct_0(sK4),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_138])])).

fof(f2061,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)),k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))
    | spl7_257
    | ~ spl7_259 ),
    inference(forward_demodulation,[],[f2047,f2058])).

fof(f2058,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK6,sK5)) = k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ spl7_259 ),
    inference(avatar_component_clause,[],[f2056])).

fof(f2056,plain,
    ( spl7_259
  <=> u1_struct_0(k2_tsep_1(sK3,sK6,sK5)) = k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_259])])).

fof(f2047,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)),u1_struct_0(k2_tsep_1(sK3,sK6,sK5)))
    | spl7_257 ),
    inference(avatar_component_clause,[],[f2045])).

fof(f2045,plain,
    ( spl7_257
  <=> r1_tarski(k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)),u1_struct_0(k2_tsep_1(sK3,sK6,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_257])])).

fof(f2059,plain,
    ( spl7_259
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_11
    | spl7_13
    | spl7_67
    | ~ spl7_68
    | ~ spl7_69
    | spl7_218 ),
    inference(avatar_split_clause,[],[f2054,f1731,f695,f690,f685,f145,f135,f120,f115,f110,f105,f2056])).

fof(f105,plain,
    ( spl7_5
  <=> m1_pre_topc(sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f110,plain,
    ( spl7_6
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f115,plain,
    ( spl7_7
  <=> m1_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f120,plain,
    ( spl7_8
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f135,plain,
    ( spl7_11
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f145,plain,
    ( spl7_13
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f685,plain,
    ( spl7_67
  <=> v2_struct_0(k2_tsep_1(sK3,sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f690,plain,
    ( spl7_68
  <=> v1_pre_topc(k2_tsep_1(sK3,sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f695,plain,
    ( spl7_69
  <=> m1_pre_topc(k2_tsep_1(sK3,sK6,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f1731,plain,
    ( spl7_218
  <=> r1_tsep_1(sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_218])])).

fof(f2054,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK6,sK5)) = k3_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_11
    | spl7_13
    | spl7_67
    | ~ spl7_68
    | ~ spl7_69
    | spl7_218 ),
    inference(forward_demodulation,[],[f1904,f75])).

fof(f1904,plain,
    ( k3_xboole_0(u1_struct_0(sK6),u1_struct_0(sK5)) = u1_struct_0(k2_tsep_1(sK3,sK6,sK5))
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_11
    | spl7_13
    | spl7_67
    | ~ spl7_68
    | ~ spl7_69
    | spl7_218 ),
    inference(unit_resulting_resolution,[],[f147,f137,f112,f122,f107,f117,f1733,f687,f692,f697,f84])).

fof(f84,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f697,plain,
    ( m1_pre_topc(k2_tsep_1(sK3,sK6,sK5),sK3)
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f695])).

fof(f692,plain,
    ( v1_pre_topc(k2_tsep_1(sK3,sK6,sK5))
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f690])).

fof(f687,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK3,sK6,sK5))
    | spl7_67 ),
    inference(avatar_component_clause,[],[f685])).

fof(f1733,plain,
    ( ~ r1_tsep_1(sK6,sK5)
    | spl7_218 ),
    inference(avatar_component_clause,[],[f1731])).

fof(f117,plain,
    ( m1_pre_topc(sK5,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f107,plain,
    ( m1_pre_topc(sK6,sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f122,plain,
    ( ~ v2_struct_0(sK5)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f112,plain,
    ( ~ v2_struct_0(sK6)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f137,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f147,plain,
    ( ~ v2_struct_0(sK3)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f2048,plain,
    ( ~ spl7_257
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_62
    | ~ spl7_69
    | spl7_137
    | ~ spl7_214 ),
    inference(avatar_split_clause,[],[f2043,f1686,f1165,f695,f631,f140,f135,f2045])).

fof(f140,plain,
    ( spl7_12
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f631,plain,
    ( spl7_62
  <=> m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f1165,plain,
    ( spl7_137
  <=> m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),k2_tsep_1(sK3,sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_137])])).

fof(f1686,plain,
    ( spl7_214
  <=> u1_struct_0(k2_tsep_1(sK3,sK4,sK5)) = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_214])])).

fof(f2043,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)),u1_struct_0(k2_tsep_1(sK3,sK6,sK5)))
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_62
    | ~ spl7_69
    | spl7_137
    | ~ spl7_214 ),
    inference(forward_demodulation,[],[f1907,f1688])).

fof(f1688,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK4,sK5)) = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ spl7_214 ),
    inference(avatar_component_clause,[],[f1686])).

fof(f1907,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK3,sK4,sK5)),u1_struct_0(k2_tsep_1(sK3,sK6,sK5)))
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_62
    | ~ spl7_69
    | spl7_137 ),
    inference(unit_resulting_resolution,[],[f142,f137,f633,f1167,f697,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f1167,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),k2_tsep_1(sK3,sK6,sK5))
    | spl7_137 ),
    inference(avatar_component_clause,[],[f1165])).

fof(f633,plain,
    ( m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f631])).

fof(f142,plain,
    ( v2_pre_topc(sK3)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f1750,plain,
    ( ~ spl7_218
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_13
    | spl7_15
    | ~ spl7_136 ),
    inference(avatar_split_clause,[],[f1712,f1160,f157,f145,f140,f135,f130,f125,f120,f115,f110,f105,f1731])).

fof(f125,plain,
    ( spl7_9
  <=> m1_pre_topc(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f130,plain,
    ( spl7_10
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f157,plain,
    ( spl7_15
  <=> sP1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f1160,plain,
    ( spl7_136
  <=> m1_pre_topc(sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_136])])).

fof(f1712,plain,
    ( ~ r1_tsep_1(sK6,sK5)
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_13
    | spl7_15
    | ~ spl7_136 ),
    inference(unit_resulting_resolution,[],[f147,f142,f137,f132,f122,f112,f127,f107,f117,f159,f1162,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X1,X3)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | sP1(X1,X3)
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f20,f32])).

fof(f32,plain,(
    ! [X1,X3] :
      ( ( r1_tsep_1(X3,X1)
        & r1_tsep_1(X1,X3) )
      | ~ sP1(X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f1162,plain,
    ( m1_pre_topc(sK4,sK6)
    | ~ spl7_136 ),
    inference(avatar_component_clause,[],[f1160])).

fof(f159,plain,
    ( ~ sP1(sK4,sK5)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f157])).

fof(f127,plain,
    ( m1_pre_topc(sK4,sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f132,plain,
    ( ~ v2_struct_0(sK4)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1706,plain,
    ( ~ spl7_136
    | ~ spl7_18
    | spl7_138 ),
    inference(avatar_split_clause,[],[f1190,f1182,f180,f1160])).

fof(f180,plain,
    ( spl7_18
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f1190,plain,
    ( ~ m1_pre_topc(sK4,sK6)
    | ~ spl7_18
    | spl7_138 ),
    inference(unit_resulting_resolution,[],[f182,f1184,f252])).

fof(f252,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f66,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f1184,plain,
    ( ~ r1_tarski(u1_struct_0(sK4),u1_struct_0(sK6))
    | spl7_138 ),
    inference(avatar_component_clause,[],[f1182])).

fof(f182,plain,
    ( l1_pre_topc(sK6)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f1693,plain,
    ( ~ spl7_31
    | spl7_212
    | ~ spl7_214 ),
    inference(avatar_contradiction_clause,[],[f1692])).

fof(f1692,plain,
    ( $false
    | ~ spl7_31
    | spl7_212
    | ~ spl7_214 ),
    inference(subsumption_resolution,[],[f1691,f1202])).

fof(f1202,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(X0,u1_struct_0(sK5)),k3_xboole_0(X0,u1_struct_0(sK6)))
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f317,f238])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X2),k3_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f231,f75])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X0),k3_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f79,f75])).

fof(f317,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl7_31
  <=> r1_tarski(u1_struct_0(sK5),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f1691,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)),k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK6)))
    | spl7_212
    | ~ spl7_214 ),
    inference(forward_demodulation,[],[f1678,f1688])).

fof(f1678,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK3,sK4,sK5)),k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK6)))
    | spl7_212 ),
    inference(avatar_component_clause,[],[f1676])).

fof(f1676,plain,
    ( spl7_212
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK3,sK4,sK5)),k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_212])])).

fof(f1689,plain,
    ( spl7_214
    | spl7_4
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | spl7_13
    | spl7_60
    | ~ spl7_61
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f1547,f631,f626,f621,f145,f135,f130,f125,f120,f115,f100,f1686])).

fof(f100,plain,
    ( spl7_4
  <=> r1_tsep_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f621,plain,
    ( spl7_60
  <=> v2_struct_0(k2_tsep_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f626,plain,
    ( spl7_61
  <=> v1_pre_topc(k2_tsep_1(sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f1547,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK4,sK5)) = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | spl7_4
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | spl7_13
    | spl7_60
    | ~ spl7_61
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f147,f137,f132,f122,f127,f117,f102,f623,f628,f633,f84])).

fof(f628,plain,
    ( v1_pre_topc(k2_tsep_1(sK3,sK4,sK5))
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f626])).

fof(f623,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK3,sK4,sK5))
    | spl7_60 ),
    inference(avatar_component_clause,[],[f621])).

fof(f102,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f1679,plain,
    ( ~ spl7_212
    | spl7_2
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_53
    | ~ spl7_62
    | ~ spl7_155 ),
    inference(avatar_split_clause,[],[f1674,f1312,f631,f577,f140,f135,f90,f1676])).

fof(f90,plain,
    ( spl7_2
  <=> m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),k2_tsep_1(sK3,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f577,plain,
    ( spl7_53
  <=> m1_pre_topc(k2_tsep_1(sK3,sK4,sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f1312,plain,
    ( spl7_155
  <=> u1_struct_0(k2_tsep_1(sK3,sK4,sK6)) = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_155])])).

fof(f1674,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK3,sK4,sK5)),k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK6)))
    | spl7_2
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_53
    | ~ spl7_62
    | ~ spl7_155 ),
    inference(forward_demodulation,[],[f1550,f1314])).

fof(f1314,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK4,sK6)) = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK6))
    | ~ spl7_155 ),
    inference(avatar_component_clause,[],[f1312])).

fof(f1550,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK3,sK4,sK5)),u1_struct_0(k2_tsep_1(sK3,sK4,sK6)))
    | spl7_2
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_53
    | ~ spl7_62 ),
    inference(unit_resulting_resolution,[],[f142,f137,f579,f92,f633,f73])).

fof(f92,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),k2_tsep_1(sK3,sK4,sK6))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f579,plain,
    ( m1_pre_topc(k2_tsep_1(sK3,sK4,sK6),sK3)
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f577])).

fof(f1315,plain,
    ( spl7_155
    | ~ spl7_5
    | spl7_6
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | spl7_13
    | spl7_51
    | ~ spl7_52
    | ~ spl7_53
    | spl7_66 ),
    inference(avatar_split_clause,[],[f1216,f664,f577,f572,f567,f145,f135,f130,f125,f110,f105,f1312])).

fof(f567,plain,
    ( spl7_51
  <=> v2_struct_0(k2_tsep_1(sK3,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f572,plain,
    ( spl7_52
  <=> v1_pre_topc(k2_tsep_1(sK3,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f664,plain,
    ( spl7_66
  <=> r1_tsep_1(sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f1216,plain,
    ( u1_struct_0(k2_tsep_1(sK3,sK4,sK6)) = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK6))
    | ~ spl7_5
    | spl7_6
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | spl7_13
    | spl7_51
    | ~ spl7_52
    | ~ spl7_53
    | spl7_66 ),
    inference(unit_resulting_resolution,[],[f147,f137,f132,f112,f127,f107,f666,f569,f574,f579,f84])).

fof(f574,plain,
    ( v1_pre_topc(k2_tsep_1(sK3,sK4,sK6))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f572])).

fof(f569,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK3,sK4,sK6))
    | spl7_51 ),
    inference(avatar_component_clause,[],[f567])).

fof(f666,plain,
    ( ~ r1_tsep_1(sK4,sK6)
    | spl7_66 ),
    inference(avatar_component_clause,[],[f664])).

fof(f1169,plain,
    ( spl7_136
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f1158,f86,f1160])).

fof(f86,plain,
    ( spl7_1
  <=> sP0(sK5,sK6,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1158,plain,
    ( m1_pre_topc(sK4,sK6)
    | ~ spl7_1 ),
    inference(resolution,[],[f88,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | m1_pre_topc(X3,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ m1_pre_topc(k2_tsep_1(X2,X3,X0),k2_tsep_1(X2,X1,X0))
        & m1_pre_topc(X3,X1) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X3,X0,X1] :
      ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
        & m1_pre_topc(X1,X3) )
      | ~ sP0(X2,X3,X0,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X2,X3,X0,X1] :
      ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
        & m1_pre_topc(X1,X3) )
      | ~ sP0(X2,X3,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f88,plain,
    ( sP0(sK5,sK6,sK3,sK4)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f1168,plain,
    ( ~ spl7_137
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f1156,f86,f1165])).

fof(f1156,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),k2_tsep_1(sK3,sK6,sK5))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f88,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(k2_tsep_1(X2,X3,X0),k2_tsep_1(X2,X1,X0))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f698,plain,
    ( spl7_69
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f681,f495,f695])).

fof(f495,plain,
    ( spl7_39
  <=> sP2(sK3,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f681,plain,
    ( m1_pre_topc(k2_tsep_1(sK3,sK6,sK5),sK3)
    | ~ spl7_39 ),
    inference(unit_resulting_resolution,[],[f497,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k2_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k2_tsep_1(X0,X2,X1)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f497,plain,
    ( sP2(sK3,sK5,sK6)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f495])).

fof(f693,plain,
    ( spl7_68
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f682,f495,f690])).

fof(f682,plain,
    ( v1_pre_topc(k2_tsep_1(sK3,sK6,sK5))
    | ~ spl7_39 ),
    inference(unit_resulting_resolution,[],[f497,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X2,X1))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f688,plain,
    ( ~ spl7_67
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f683,f495,f685])).

fof(f683,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK3,sK6,sK5))
    | ~ spl7_39 ),
    inference(unit_resulting_resolution,[],[f497,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X2,X1))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f670,plain,
    ( ~ spl7_66
    | ~ spl7_20
    | ~ spl7_21
    | spl7_63 ),
    inference(avatar_split_clause,[],[f669,f641,f205,f198,f664])).

fof(f198,plain,
    ( spl7_20
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f205,plain,
    ( spl7_21
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f641,plain,
    ( spl7_63
  <=> r1_tsep_1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f669,plain,
    ( ~ r1_tsep_1(sK4,sK6)
    | ~ spl7_20
    | ~ spl7_21
    | spl7_63 ),
    inference(subsumption_resolution,[],[f668,f200])).

fof(f200,plain,
    ( l1_struct_0(sK4)
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f198])).

fof(f668,plain,
    ( ~ r1_tsep_1(sK4,sK6)
    | ~ l1_struct_0(sK4)
    | ~ spl7_21
    | spl7_63 ),
    inference(subsumption_resolution,[],[f652,f207])).

fof(f207,plain,
    ( l1_struct_0(sK6)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f205])).

fof(f652,plain,
    ( ~ r1_tsep_1(sK4,sK6)
    | ~ l1_struct_0(sK6)
    | ~ l1_struct_0(sK4)
    | spl7_63 ),
    inference(resolution,[],[f643,f76])).

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f643,plain,
    ( ~ r1_tsep_1(sK6,sK4)
    | spl7_63 ),
    inference(avatar_component_clause,[],[f641])).

fof(f644,plain,
    ( ~ spl7_63
    | ~ spl7_3
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_13
    | spl7_16 ),
    inference(avatar_split_clause,[],[f635,f163,f145,f140,f135,f130,f125,f120,f115,f110,f105,f95,f641])).

fof(f95,plain,
    ( spl7_3
  <=> m1_pre_topc(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f163,plain,
    ( spl7_16
  <=> sP1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f635,plain,
    ( ~ r1_tsep_1(sK6,sK4)
    | ~ spl7_3
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | spl7_13
    | spl7_16 ),
    inference(unit_resulting_resolution,[],[f147,f142,f137,f122,f132,f112,f117,f107,f127,f97,f165,f69])).

fof(f165,plain,
    ( ~ sP1(sK5,sK4)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f97,plain,
    ( m1_pre_topc(sK5,sK6)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f634,plain,
    ( spl7_62
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f617,f490,f631])).

fof(f490,plain,
    ( spl7_38
  <=> sP2(sK3,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f617,plain,
    ( m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),sK3)
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f492,f82])).

fof(f492,plain,
    ( sP2(sK3,sK5,sK4)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f490])).

fof(f629,plain,
    ( spl7_61
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f618,f490,f626])).

fof(f618,plain,
    ( v1_pre_topc(k2_tsep_1(sK3,sK4,sK5))
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f492,f81])).

fof(f624,plain,
    ( ~ spl7_60
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f619,f490,f621])).

fof(f619,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK3,sK4,sK5))
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f492,f80])).

fof(f580,plain,
    ( spl7_53
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f563,f475,f577])).

fof(f475,plain,
    ( spl7_35
  <=> sP2(sK3,sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f563,plain,
    ( m1_pre_topc(k2_tsep_1(sK3,sK4,sK6),sK3)
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f477,f82])).

fof(f477,plain,
    ( sP2(sK3,sK6,sK4)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f475])).

fof(f575,plain,
    ( spl7_52
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f564,f475,f572])).

fof(f564,plain,
    ( v1_pre_topc(k2_tsep_1(sK3,sK4,sK6))
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f477,f81])).

fof(f570,plain,
    ( ~ spl7_51
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f565,f475,f567])).

fof(f565,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK3,sK4,sK6))
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f477,f80])).

fof(f498,plain,
    ( spl7_39
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_11
    | spl7_13 ),
    inference(avatar_split_clause,[],[f451,f145,f135,f120,f115,f110,f105,f495])).

fof(f451,plain,
    ( sP2(sK3,sK5,sK6)
    | ~ spl7_5
    | spl7_6
    | ~ spl7_7
    | spl7_8
    | ~ spl7_11
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f147,f137,f112,f107,f122,f117,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f29,f34])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f493,plain,
    ( spl7_38
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | spl7_13 ),
    inference(avatar_split_clause,[],[f452,f145,f135,f130,f125,f120,f115,f490])).

fof(f452,plain,
    ( sP2(sK3,sK5,sK4)
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f147,f137,f132,f127,f122,f117,f83])).

fof(f478,plain,
    ( spl7_35
    | ~ spl7_5
    | spl7_6
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | spl7_13 ),
    inference(avatar_split_clause,[],[f455,f145,f135,f130,f125,f110,f105,f475])).

fof(f455,plain,
    ( sP2(sK3,sK6,sK4)
    | ~ spl7_5
    | spl7_6
    | ~ spl7_9
    | spl7_10
    | ~ spl7_11
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f147,f137,f132,f127,f112,f107,f83])).

fof(f319,plain,
    ( spl7_31
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f313,f269,f315])).

fof(f269,plain,
    ( spl7_27
  <=> m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f313,plain,
    ( r1_tarski(u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ spl7_27 ),
    inference(resolution,[],[f271,f77])).

fof(f271,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f269])).

fof(f272,plain,
    ( spl7_27
    | ~ spl7_3
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f248,f180,f95,f269])).

fof(f248,plain,
    ( m1_subset_1(u1_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ spl7_3
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f182,f97,f66])).

fof(f208,plain,
    ( spl7_21
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f203,f180,f205])).

fof(f203,plain,
    ( l1_struct_0(sK6)
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f182,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f201,plain,
    ( spl7_20
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f196,f175,f198])).

fof(f175,plain,
    ( spl7_17
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f196,plain,
    ( l1_struct_0(sK4)
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f177,f64])).

fof(f177,plain,
    ( l1_pre_topc(sK4)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f175])).

fof(f195,plain,
    ( spl7_17
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f194,f135,f125,f175])).

fof(f194,plain,
    ( l1_pre_topc(sK4)
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f173,f137])).

fof(f173,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ spl7_9 ),
    inference(resolution,[],[f65,f127])).

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f193,plain,
    ( spl7_18
    | ~ spl7_5
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f192,f135,f105,f180])).

fof(f192,plain,
    ( l1_pre_topc(sK6)
    | ~ spl7_5
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f172,f137])).

fof(f172,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f65,f107])).

fof(f166,plain,
    ( ~ spl7_16
    | spl7_4 ),
    inference(avatar_split_clause,[],[f161,f100,f163])).

fof(f161,plain,
    ( ~ sP1(sK5,sK4)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f102,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tsep_1(X1,X0)
        & r1_tsep_1(X0,X1) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X3] :
      ( ( r1_tsep_1(X3,X1)
        & r1_tsep_1(X1,X3) )
      | ~ sP1(X1,X3) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f160,plain,
    ( ~ spl7_15
    | spl7_4 ),
    inference(avatar_split_clause,[],[f155,f100,f157])).

fof(f155,plain,
    ( ~ sP1(sK4,sK5)
    | spl7_4 ),
    inference(unit_resulting_resolution,[],[f102,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f148,plain,(
    ~ spl7_13 ),
    inference(avatar_split_clause,[],[f52,f145])).

fof(f52,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),k2_tsep_1(sK3,sK4,sK6))
        & m1_pre_topc(sK5,sK6) )
      | sP0(sK5,sK6,sK3,sK4) )
    & ~ r1_tsep_1(sK4,sK5)
    & m1_pre_topc(sK6,sK3)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK3)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK3)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f31,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                        & m1_pre_topc(X2,X3) )
                      | sP0(X2,X3,X0,X1) )
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
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(sK3,X1,X2),k2_tsep_1(sK3,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | sP0(X2,X3,sK3,X1) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK3)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK3)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK3)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ m1_pre_topc(k2_tsep_1(sK3,X1,X2),k2_tsep_1(sK3,X1,X3))
                    & m1_pre_topc(X2,X3) )
                  | sP0(X2,X3,sK3,X1) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK3)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK3)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK3)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,X2),k2_tsep_1(sK3,sK4,X3))
                  & m1_pre_topc(X2,X3) )
                | sP0(X2,X3,sK3,sK4) )
              & ~ r1_tsep_1(sK4,X2)
              & m1_pre_topc(X3,sK3)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK3)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK4,sK3)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,X2),k2_tsep_1(sK3,sK4,X3))
                & m1_pre_topc(X2,X3) )
              | sP0(X2,X3,sK3,sK4) )
            & ~ r1_tsep_1(sK4,X2)
            & m1_pre_topc(X3,sK3)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK3)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),k2_tsep_1(sK3,sK4,X3))
              & m1_pre_topc(sK5,X3) )
            | sP0(sK5,X3,sK3,sK4) )
          & ~ r1_tsep_1(sK4,sK5)
          & m1_pre_topc(X3,sK3)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK5,sK3)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ( ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),k2_tsep_1(sK3,sK4,X3))
            & m1_pre_topc(sK5,X3) )
          | sP0(sK5,X3,sK3,sK4) )
        & ~ r1_tsep_1(sK4,sK5)
        & m1_pre_topc(X3,sK3)
        & ~ v2_struct_0(X3) )
   => ( ( ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),k2_tsep_1(sK3,sK4,sK6))
          & m1_pre_topc(sK5,sK6) )
        | sP0(sK5,sK6,sK3,sK4) )
      & ~ r1_tsep_1(sK4,sK5)
      & m1_pre_topc(sK6,sK3)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | sP0(X2,X3,X0,X1) )
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
    inference(definition_folding,[],[f15,f30])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
                     => ( ( m1_pre_topc(X2,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                        & ( m1_pre_topc(X1,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
                   => ( ( m1_pre_topc(X2,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                      & ( m1_pre_topc(X1,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tmap_1)).

fof(f143,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f53,f140])).

fof(f53,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f138,plain,(
    spl7_11 ),
    inference(avatar_split_clause,[],[f54,f135])).

fof(f54,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f133,plain,(
    ~ spl7_10 ),
    inference(avatar_split_clause,[],[f55,f130])).

fof(f55,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f128,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f56,f125])).

fof(f56,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,(
    ~ spl7_8 ),
    inference(avatar_split_clause,[],[f57,f120])).

fof(f57,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f58,f115])).

fof(f58,plain,(
    m1_pre_topc(sK5,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    ~ spl7_6 ),
    inference(avatar_split_clause,[],[f59,f110])).

fof(f59,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f60,f105])).

fof(f60,plain,(
    m1_pre_topc(sK6,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f61,f100])).

fof(f61,plain,(
    ~ r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,
    ( spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f62,f95,f86])).

fof(f62,plain,
    ( m1_pre_topc(sK5,sK6)
    | sP0(sK5,sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f63,f90,f86])).

fof(f63,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK3,sK4,sK5),k2_tsep_1(sK3,sK4,sK6))
    | sP0(sK5,sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

%------------------------------------------------------------------------------
