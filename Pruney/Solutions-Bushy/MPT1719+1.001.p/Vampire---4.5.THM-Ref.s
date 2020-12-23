%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1719+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 618 expanded)
%              Number of leaves         :   56 ( 303 expanded)
%              Depth                    :   11
%              Number of atoms          :  879 (4046 expanded)
%              Number of equality atoms :   27 (  46 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12007)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f3040,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f187,f190,f192,f194,f203,f212,f220,f228,f239,f247,f256,f362,f367,f418,f549,f599,f669,f674,f679,f970,f975,f980,f1196,f1473,f1617,f3039])).

fof(f3039,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_9
    | spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_50
    | ~ spl6_92
    | spl6_140
    | ~ spl6_141
    | ~ spl6_142
    | ~ spl6_206 ),
    inference(avatar_contradiction_clause,[],[f3038])).

fof(f3038,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_9
    | spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_50
    | ~ spl6_92
    | spl6_140
    | ~ spl6_141
    | ~ spl6_142
    | ~ spl6_206 ),
    inference(subsumption_resolution,[],[f3037,f417])).

fof(f417,plain,
    ( r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl6_50
  <=> r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f3037,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)))
    | spl6_1
    | spl6_2
    | ~ spl6_9
    | spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_92
    | spl6_140
    | ~ spl6_141
    | ~ spl6_142
    | ~ spl6_206 ),
    inference(forward_demodulation,[],[f2832,f1616])).

fof(f1616,plain,
    ( u1_struct_0(k2_tsep_1(sK1,sK4,sK5)) = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ spl6_206 ),
    inference(avatar_component_clause,[],[f1614])).

fof(f1614,plain,
    ( spl6_206
  <=> u1_struct_0(k2_tsep_1(sK1,sK4,sK5)) = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_206])])).

fof(f2832,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),u1_struct_0(k2_tsep_1(sK1,sK4,sK5)))
    | spl6_1
    | spl6_2
    | ~ spl6_9
    | spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_13
    | ~ spl6_14
    | spl6_15
    | ~ spl6_92
    | spl6_140
    | ~ spl6_141
    | ~ spl6_142 ),
    inference(unit_resulting_resolution,[],[f145,f135,f130,f140,f120,f135,f125,f115,f80,f969,f974,f678,f75,f979,f979,f1058])).

fof(f1058,plain,(
    ! [X37,X35,X38,X36,X34] :
      ( ~ r1_tarski(k3_xboole_0(u1_struct_0(X35),u1_struct_0(X36)),u1_struct_0(X37))
      | m1_pre_topc(k2_tsep_1(X34,X35,X36),X37)
      | ~ m1_pre_topc(X37,X38)
      | ~ m1_pre_topc(k2_tsep_1(X34,X35,X36),X38)
      | ~ l1_pre_topc(X38)
      | ~ v2_pre_topc(X38)
      | ~ m1_pre_topc(k2_tsep_1(X34,X35,X36),X34)
      | ~ v1_pre_topc(k2_tsep_1(X34,X35,X36))
      | v2_struct_0(k2_tsep_1(X34,X35,X36))
      | r1_tsep_1(X35,X36)
      | ~ m1_pre_topc(X36,X34)
      | v2_struct_0(X36)
      | ~ m1_pre_topc(X35,X34)
      | v2_struct_0(X35)
      | ~ l1_pre_topc(X34)
      | v2_struct_0(X34) ) ),
    inference(superposition,[],[f62,f71])).

fof(f71,plain,(
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
    inference(equality_resolution,[],[f60])).

% (12010)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f60,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f979,plain,
    ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1)
    | ~ spl6_142 ),
    inference(avatar_component_clause,[],[f977])).

fof(f977,plain,
    ( spl6_142
  <=> m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_142])])).

fof(f75,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),k2_tsep_1(sK1,sK4,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_1
  <=> m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),k2_tsep_1(sK1,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f678,plain,
    ( m1_pre_topc(k2_tsep_1(sK1,sK4,sK5),sK1)
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f676])).

fof(f676,plain,
    ( spl6_92
  <=> m1_pre_topc(k2_tsep_1(sK1,sK4,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f974,plain,
    ( v1_pre_topc(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl6_141 ),
    inference(avatar_component_clause,[],[f972])).

fof(f972,plain,
    ( spl6_141
  <=> v1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_141])])).

fof(f969,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | spl6_140 ),
    inference(avatar_component_clause,[],[f967])).

fof(f967,plain,
    ( spl6_140
  <=> v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_140])])).

fof(f80,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_2
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f115,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_9
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f125,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_11
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f120,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_10
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f140,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl6_14
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f130,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl6_12
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f135,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_13
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f145,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_15
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f1617,plain,
    ( spl6_206
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_13
    | spl6_15
    | spl6_90
    | ~ spl6_91
    | ~ spl6_92
    | spl6_184 ),
    inference(avatar_split_clause,[],[f1541,f1467,f676,f671,f666,f143,f133,f108,f103,f98,f93,f1614])).

fof(f93,plain,
    ( spl6_5
  <=> m1_pre_topc(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f98,plain,
    ( spl6_6
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f103,plain,
    ( spl6_7
  <=> m1_pre_topc(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f108,plain,
    ( spl6_8
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f666,plain,
    ( spl6_90
  <=> v2_struct_0(k2_tsep_1(sK1,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f671,plain,
    ( spl6_91
  <=> v1_pre_topc(k2_tsep_1(sK1,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f1467,plain,
    ( spl6_184
  <=> r1_tsep_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_184])])).

fof(f1541,plain,
    ( u1_struct_0(k2_tsep_1(sK1,sK4,sK5)) = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_13
    | spl6_15
    | spl6_90
    | ~ spl6_91
    | ~ spl6_92
    | spl6_184 ),
    inference(unit_resulting_resolution,[],[f145,f135,f110,f100,f105,f95,f1469,f668,f673,f678,f71])).

fof(f673,plain,
    ( v1_pre_topc(k2_tsep_1(sK1,sK4,sK5))
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f671])).

fof(f668,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK1,sK4,sK5))
    | spl6_90 ),
    inference(avatar_component_clause,[],[f666])).

fof(f1469,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | spl6_184 ),
    inference(avatar_component_clause,[],[f1467])).

fof(f95,plain,
    ( m1_pre_topc(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f105,plain,
    ( m1_pre_topc(sK4,sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f100,plain,
    ( ~ v2_struct_0(sK5)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f110,plain,
    ( ~ v2_struct_0(sK4)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1473,plain,
    ( ~ spl6_184
    | ~ spl6_21
    | ~ spl6_22
    | spl6_175 ),
    inference(avatar_split_clause,[],[f1472,f1193,f208,f199,f1467])).

fof(f199,plain,
    ( spl6_21
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f208,plain,
    ( spl6_22
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f1193,plain,
    ( spl6_175
  <=> r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_175])])).

fof(f1472,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | ~ spl6_21
    | ~ spl6_22
    | spl6_175 ),
    inference(subsumption_resolution,[],[f1471,f210])).

fof(f210,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f208])).

fof(f1471,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK4)
    | ~ spl6_21
    | spl6_175 ),
    inference(subsumption_resolution,[],[f1460,f201])).

fof(f201,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f199])).

fof(f1460,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4)
    | spl6_175 ),
    inference(resolution,[],[f1195,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f1195,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | spl6_175 ),
    inference(avatar_component_clause,[],[f1193])).

fof(f1196,plain,
    ( ~ spl6_175
    | spl6_27
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f1187,f364,f359,f253,f1193])).

fof(f253,plain,
    ( spl6_27
  <=> r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f359,plain,
    ( spl6_42
  <=> r1_tarski(u1_struct_0(sK3),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f364,plain,
    ( spl6_43
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f1187,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | spl6_27
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(unit_resulting_resolution,[],[f366,f361,f255,f259])).

fof(f259,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X2,X3),k1_xboole_0)
      | ~ r1_tarski(X3,X1)
      | ~ r1_tarski(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f70,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

fof(f255,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),k1_xboole_0)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f253])).

fof(f361,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f359])).

fof(f366,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f364])).

fof(f980,plain,
    ( spl6_142
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f963,f596,f977])).

fof(f596,plain,
    ( spl6_78
  <=> sP0(sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f963,plain,
    ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1)
    | ~ spl6_78 ),
    inference(unit_resulting_resolution,[],[f598,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k2_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k2_tsep_1(X0,X2,X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f598,plain,
    ( sP0(sK1,sK3,sK2)
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f596])).

fof(f975,plain,
    ( spl6_141
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f964,f596,f972])).

fof(f964,plain,
    ( v1_pre_topc(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl6_78 ),
    inference(unit_resulting_resolution,[],[f598,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f970,plain,
    ( ~ spl6_140
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f965,f596,f967])).

fof(f965,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl6_78 ),
    inference(unit_resulting_resolution,[],[f598,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f679,plain,
    ( spl6_92
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f662,f546,f676])).

fof(f546,plain,
    ( spl6_68
  <=> sP0(sK1,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f662,plain,
    ( m1_pre_topc(k2_tsep_1(sK1,sK4,sK5),sK1)
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f548,f68])).

fof(f548,plain,
    ( sP0(sK1,sK5,sK4)
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f546])).

fof(f674,plain,
    ( spl6_91
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f663,f546,f671])).

% (12004)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f663,plain,
    ( v1_pre_topc(k2_tsep_1(sK1,sK4,sK5))
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f548,f67])).

fof(f669,plain,
    ( ~ spl6_90
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f664,f546,f666])).

fof(f664,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK1,sK4,sK5))
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f548,f66])).

fof(f599,plain,
    ( spl6_78
    | ~ spl6_9
    | spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_13
    | spl6_15 ),
    inference(avatar_split_clause,[],[f528,f143,f133,f128,f123,f118,f113,f596])).

fof(f528,plain,
    ( sP0(sK1,sK3,sK2)
    | ~ spl6_9
    | spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_13
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f145,f135,f130,f125,f120,f115,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f26])).

% (12014)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f549,plain,
    ( spl6_68
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_13
    | spl6_15 ),
    inference(avatar_split_clause,[],[f538,f143,f133,f108,f103,f98,f93,f546])).

fof(f538,plain,
    ( sP0(sK1,sK5,sK4)
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | spl6_8
    | ~ spl6_13
    | spl6_15 ),
    inference(unit_resulting_resolution,[],[f145,f135,f110,f105,f100,f95,f69])).

fof(f418,plain,
    ( spl6_50
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f392,f364,f359,f415])).

fof(f392,plain,
    ( r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)))
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(unit_resulting_resolution,[],[f361,f366,f70])).

fof(f367,plain,
    ( spl6_43
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f355,f138,f133,f123,f103,f88,f364])).

fof(f88,plain,
    ( spl6_4
  <=> m1_pre_topc(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f355,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f140,f135,f125,f105,f90,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,
    ( m1_pre_topc(sK2,sK4)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f362,plain,
    ( spl6_42
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f356,f138,f133,f113,f93,f83,f359])).

fof(f83,plain,
    ( spl6_3
  <=> m1_pre_topc(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f356,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f140,f135,f115,f95,f85,f63])).

fof(f85,plain,
    ( m1_pre_topc(sK3,sK5)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f256,plain,
    ( ~ spl6_27
    | spl6_26 ),
    inference(avatar_split_clause,[],[f248,f244,f253])).

fof(f244,plain,
    ( spl6_26
  <=> k1_xboole_0 = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f248,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),k1_xboole_0)
    | spl6_26 ),
    inference(unit_resulting_resolution,[],[f246,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f246,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f244])).

fof(f247,plain,
    ( ~ spl6_26
    | spl6_25 ),
    inference(avatar_split_clause,[],[f241,f236,f244])).

fof(f236,plain,
    ( spl6_25
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f241,plain,
    ( k1_xboole_0 != k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | spl6_25 ),
    inference(unit_resulting_resolution,[],[f238,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f238,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f236])).

fof(f239,plain,
    ( ~ spl6_25
    | spl6_2
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f232,f224,f216,f78,f236])).

% (12012)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f216,plain,
    ( spl6_23
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f224,plain,
    ( spl6_24
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f232,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | spl6_2
    | ~ spl6_23
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f226,f218,f80,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f218,plain,
    ( l1_struct_0(sK3)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f226,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f224])).

fof(f228,plain,
    ( spl6_24
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f222,f181,f224])).

fof(f181,plain,
    ( spl6_20
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f222,plain,
    ( l1_struct_0(sK2)
    | ~ spl6_20 ),
    inference(resolution,[],[f183,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f183,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f220,plain,
    ( spl6_23
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f214,f176,f216])).

fof(f176,plain,
    ( spl6_19
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f214,plain,
    ( l1_struct_0(sK3)
    | ~ spl6_19 ),
    inference(resolution,[],[f178,f57])).

fof(f178,plain,
    ( l1_pre_topc(sK3)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f212,plain,
    ( spl6_22
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f206,f171,f208])).

fof(f171,plain,
    ( spl6_18
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f206,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_18 ),
    inference(resolution,[],[f173,f57])).

fof(f173,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f171])).

fof(f203,plain,
    ( spl6_21
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f197,f166,f199])).

fof(f166,plain,
    ( spl6_17
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f197,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_17 ),
    inference(resolution,[],[f168,f57])).

fof(f168,plain,
    ( l1_pre_topc(sK5)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f166])).

fof(f194,plain,
    ( spl6_17
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f193,f133,f93,f166])).

fof(f193,plain,
    ( l1_pre_topc(sK5)
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f164,f135])).

fof(f164,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f58,f95])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f192,plain,
    ( spl6_18
    | ~ spl6_7
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f191,f133,f103,f171])).

fof(f191,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_7
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f163,f135])).

fof(f163,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f58,f105])).

fof(f190,plain,
    ( spl6_19
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f189,f133,f113,f176])).

fof(f189,plain,
    ( l1_pre_topc(sK3)
    | ~ spl6_9
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f162,f135])).

fof(f162,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl6_9 ),
    inference(resolution,[],[f58,f115])).

fof(f187,plain,
    ( spl6_20
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f186,f133,f123,f181])).

fof(f186,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_11
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f160,f135])).

fof(f160,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ spl6_11 ),
    inference(resolution,[],[f58,f125])).

fof(f146,plain,(
    ~ spl6_15 ),
    inference(avatar_split_clause,[],[f40,f143])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),k2_tsep_1(sK1,sK4,sK5))
    & ~ r1_tsep_1(sK2,sK3)
    & m1_pre_topc(sK3,sK5)
    & m1_pre_topc(sK2,sK4)
    & m1_pre_topc(sK5,sK1)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f13,f32,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                        & ~ r1_tsep_1(X1,X2)
                        & m1_pre_topc(X2,X4)
                        & m1_pre_topc(X1,X3)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(sK1,X1,X2),k2_tsep_1(sK1,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,sK1)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ m1_pre_topc(k2_tsep_1(sK1,X1,X2),k2_tsep_1(sK1,X3,X4))
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X4)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X4,sK1)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,X2),k2_tsep_1(sK1,X3,X4))
                  & ~ r1_tsep_1(sK2,X2)
                  & m1_pre_topc(X2,X4)
                  & m1_pre_topc(sK2,X3)
                  & m1_pre_topc(X4,sK1)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,X2),k2_tsep_1(sK1,X3,X4))
                & ~ r1_tsep_1(sK2,X2)
                & m1_pre_topc(X2,X4)
                & m1_pre_topc(sK2,X3)
                & m1_pre_topc(X4,sK1)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),k2_tsep_1(sK1,X3,X4))
              & ~ r1_tsep_1(sK2,sK3)
              & m1_pre_topc(sK3,X4)
              & m1_pre_topc(sK2,X3)
              & m1_pre_topc(X4,sK1)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),k2_tsep_1(sK1,X3,X4))
            & ~ r1_tsep_1(sK2,sK3)
            & m1_pre_topc(sK3,X4)
            & m1_pre_topc(sK2,X3)
            & m1_pre_topc(X4,sK1)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),k2_tsep_1(sK1,sK4,X4))
          & ~ r1_tsep_1(sK2,sK3)
          & m1_pre_topc(sK3,X4)
          & m1_pre_topc(sK2,sK4)
          & m1_pre_topc(X4,sK1)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK4,sK1)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X4] :
        ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),k2_tsep_1(sK1,sK4,X4))
        & ~ r1_tsep_1(sK2,sK3)
        & m1_pre_topc(sK3,X4)
        & m1_pre_topc(sK2,sK4)
        & m1_pre_topc(X4,sK1)
        & ~ v2_struct_0(X4) )
   => ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),k2_tsep_1(sK1,sK4,sK5))
      & ~ r1_tsep_1(sK2,sK3)
      & m1_pre_topc(sK3,sK5)
      & m1_pre_topc(sK2,sK4)
      & m1_pre_topc(sK5,sK1)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X2,X4)
                            & m1_pre_topc(X1,X3) )
                         => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                            | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

fof(f141,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f41,f138])).

fof(f41,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f136,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f42,f133])).

fof(f42,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f131,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f43,f128])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f126,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f44,f123])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f121,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f45,f118])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f116,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f46,f113])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f111,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f47,f108])).

fof(f47,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f48,f103])).

fof(f48,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f101,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f50,f93])).

fof(f50,plain,(
    m1_pre_topc(sK5,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f91,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f51,f88])).

fof(f51,plain,(
    m1_pre_topc(sK2,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f52,f83])).

fof(f52,plain,(
    m1_pre_topc(sK3,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f53,f78])).

fof(f53,plain,(
    ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f54,f73])).

fof(f54,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),k2_tsep_1(sK1,sK4,sK5)) ),
    inference(cnf_transformation,[],[f33])).

%------------------------------------------------------------------------------
