%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:53 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 668 expanded)
%              Number of leaves         :   43 ( 280 expanded)
%              Depth                    :   11
%              Number of atoms          :  483 (1760 expanded)
%              Number of equality atoms :   70 ( 239 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1992,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f77,f152,f157,f243,f255,f260,f265,f270,f286,f355,f360,f365,f423,f428,f508,f806,f926,f1372,f1377,f1382,f1387,f1396,f1401,f1406,f1580,f1585,f1591,f1761,f1766,f1971,f1991])).

fof(f1991,plain,
    ( spl3_14
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f1990])).

fof(f1990,plain,
    ( $false
    | spl3_14
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f1983,f354])).

fof(f354,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl3_14
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1983,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)))
    | ~ spl3_31 ),
    inference(superposition,[],[f61,f1760])).

fof(f1760,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f1758])).

fof(f1758,plain,
    ( spl3_31
  <=> k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f1971,plain,
    ( spl3_33
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f1960,f1393,f1968])).

fof(f1968,plain,
    ( spl3_33
  <=> r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k2_xboole_0(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1393,plain,
    ( spl3_25
  <=> k2_pre_topc(sK0,k2_xboole_0(sK2,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f1960,plain,
    ( r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k2_xboole_0(sK2,sK2)))
    | ~ spl3_25 ),
    inference(superposition,[],[f61,f1395])).

fof(f1395,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK2,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f1393])).

fof(f1766,plain,
    ( spl3_32
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f226,f154,f149,f54,f49,f44,f39,f1763])).

fof(f1763,plain,
    ( spl3_32
  <=> k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f39,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f49,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f149,plain,
    ( spl3_6
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f154,plain,
    ( spl3_7
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f226,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f209,f94])).

fof(f94,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f90,f85])).

fof(f85,plain,
    ( k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f56,f51,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f51,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f90,plain,
    ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f41,f46,f51,f56,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).

fof(f46,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f41,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f209,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f151,f156,f37])).

fof(f156,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f151,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f149])).

fof(f1761,plain,
    ( spl3_31
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f224,f154,f149,f54,f49,f44,f39,f1758])).

fof(f224,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f215,f95])).

fof(f95,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f89,f86])).

fof(f86,plain,
    ( k2_xboole_0(sK2,sK1) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f51,f56,f37])).

fof(f89,plain,
    ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f41,f46,f56,f51,f29])).

fof(f215,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f151,f156,f37])).

fof(f1591,plain,
    ( spl3_30
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f223,f154,f54,f44,f39,f1588])).

fof(f1588,plain,
    ( spl3_30
  <=> k2_pre_topc(sK0,k2_xboole_0(sK1,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f223,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f216,f93])).

fof(f93,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f91,f87])).

fof(f87,plain,
    ( k2_xboole_0(sK1,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f56,f56,f37])).

fof(f91,plain,
    ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f41,f46,f56,f56,f29])).

fof(f216,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f156,f156,f37])).

fof(f1585,plain,
    ( spl3_29
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f218,f154,f49,f1582])).

fof(f1582,plain,
    ( spl3_29
  <=> k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f218,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f51,f156,f37])).

fof(f1580,plain,
    ( spl3_28
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f217,f154,f54,f1577])).

fof(f1577,plain,
    ( spl3_28
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f217,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f56,f156,f37])).

fof(f1406,plain,
    ( spl3_27
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f212,f154,f49,f1403])).

fof(f1403,plain,
    ( spl3_27
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f212,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK2)
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f51,f156,f37])).

fof(f1401,plain,
    ( spl3_26
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f211,f154,f54,f1398])).

fof(f1398,plain,
    ( spl3_26
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f211,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f56,f156,f37])).

fof(f1396,plain,
    ( spl3_25
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f182,f149,f49,f44,f39,f1393])).

fof(f182,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK2,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f176,f96])).

fof(f96,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK2,sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f88,f84])).

fof(f84,plain,
    ( k2_xboole_0(sK2,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,sK2)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f51,f51,f37])).

fof(f88,plain,
    ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f41,f46,f51,f51,f29])).

fof(f176,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f151,f151,f37])).

fof(f1387,plain,
    ( spl3_24
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f178,f149,f49,f1384])).

fof(f1384,plain,
    ( spl3_24
  <=> k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK2)) = k2_xboole_0(sK2,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f178,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK2)) = k2_xboole_0(sK2,k2_pre_topc(sK0,sK2))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f51,f151,f37])).

fof(f1382,plain,
    ( spl3_23
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f177,f149,f54,f1379])).

fof(f1379,plain,
    ( spl3_23
  <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f177,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK2))
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f56,f151,f37])).

fof(f1377,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f173,f149,f49,f1374])).

fof(f1374,plain,
    ( spl3_22
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK2) = k2_xboole_0(k2_pre_topc(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f173,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK2) = k2_xboole_0(k2_pre_topc(sK0,sK2),sK2)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f51,f151,f37])).

fof(f1372,plain,
    ( spl3_21
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f172,f149,f54,f1369])).

fof(f1369,plain,
    ( spl3_21
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1) = k2_xboole_0(k2_pre_topc(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f172,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1) = k2_xboole_0(k2_pre_topc(sK0,sK2),sK1)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f56,f151,f37])).

fof(f926,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f206,f154,f44,f923])).

fof(f923,plain,
    ( spl3_20
  <=> m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f206,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f46,f156,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f806,plain,
    ( spl3_19
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f168,f149,f44,f803])).

fof(f803,plain,
    ( spl3_19
  <=> m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f168,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f46,f151,f32])).

fof(f508,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_5 ),
    inference(avatar_split_clause,[],[f81,f74,f240,f154])).

fof(f240,plain,
    ( spl3_8
  <=> r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f74,plain,
    ( spl3_5
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f81,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(superposition,[],[f76,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f76,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f428,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f96,f49,f44,f39,f425])).

fof(f425,plain,
    ( spl3_18
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f423,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f95,f54,f49,f44,f39,f420])).

fof(f420,plain,
    ( spl3_17
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f365,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f94,f54,f49,f44,f39,f362])).

fof(f362,plain,
    ( spl3_16
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f360,plain,
    ( spl3_15
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f93,f54,f44,f39,f357])).

fof(f357,plain,
    ( spl3_15
  <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f355,plain,
    ( ~ spl3_14
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_13 ),
    inference(avatar_split_clause,[],[f333,f283,f149,f54,f49,f44,f39,f352])).

fof(f283,plain,
    ( spl3_13
  <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f333,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_13 ),
    inference(forward_demodulation,[],[f332,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f332,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_13 ),
    inference(backward_demodulation,[],[f285,f331])).

fof(f331,plain,
    ( ! [X0] : k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f321,f119])).

fof(f119,plain,
    ( ! [X0] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f98,f108])).

fof(f108,plain,
    ( ! [X0] : k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f51,f71,f37])).

fof(f71,plain,
    ( ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f65,f67])).

fof(f67,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f56,f34])).

fof(f65,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f56,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f98,plain,
    ( ! [X0] : k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f46,f41,f51,f71,f29])).

fof(f321,plain,
    ( ! [X0] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f151,f104,f37])).

fof(f104,plain,
    ( ! [X0] : m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f46,f71,f32])).

fof(f285,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f283])).

fof(f286,plain,
    ( ~ spl3_13
    | spl3_8 ),
    inference(avatar_split_clause,[],[f244,f240,f283])).

fof(f244,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))))
    | spl3_8 ),
    inference(unit_resulting_resolution,[],[f242,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f242,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f240])).

fof(f270,plain,
    ( spl3_12
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f87,f54,f267])).

fof(f267,plain,
    ( spl3_12
  <=> k2_xboole_0(sK1,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f265,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f86,f54,f49,f262])).

fof(f262,plain,
    ( spl3_11
  <=> k2_xboole_0(sK2,sK1) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f260,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f85,f54,f49,f257])).

fof(f257,plain,
    ( spl3_10
  <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f255,plain,
    ( spl3_9
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f84,f49,f252])).

fof(f252,plain,
    ( spl3_9
  <=> k2_xboole_0(sK2,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f243,plain,
    ( ~ spl3_8
    | spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f222,f154,f74,f240])).

fof(f222,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_5
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f76,f219])).

fof(f219,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f156,f34])).

fof(f157,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f83,f54,f44,f154])).

fof(f83,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f46,f56,f32])).

fof(f152,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f82,f49,f44,f149])).

fof(f82,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f46,f51,f32])).

fof(f77,plain,
    ( ~ spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f70,f54,f74])).

fof(f70,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f25,f67])).

fof(f25,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).

fof(f57,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f26,f54])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f44])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f39])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (26032)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (26039)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (26027)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (26028)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (26029)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (26029)Refutation not found, incomplete strategy% (26029)------------------------------
% 0.21/0.51  % (26029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26029)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26029)Memory used [KB]: 10490
% 0.21/0.51  % (26029)Time elapsed: 0.086 s
% 0.21/0.51  % (26029)------------------------------
% 0.21/0.51  % (26029)------------------------------
% 0.21/0.51  % (26049)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (26043)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (26041)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (26040)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (26031)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (26042)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (26035)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (26036)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (26033)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (26048)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (26034)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (26046)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (26026)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.52  % (26044)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (26049)Refutation not found, incomplete strategy% (26049)------------------------------
% 0.21/0.53  % (26049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26049)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (26049)Memory used [KB]: 10618
% 0.21/0.53  % (26049)Time elapsed: 0.069 s
% 0.21/0.53  % (26049)------------------------------
% 0.21/0.53  % (26049)------------------------------
% 0.21/0.53  % (26047)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (26038)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.53  % (26045)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.54  % (26030)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.54  % (26037)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 2.16/0.64  % (26048)Refutation not found, incomplete strategy% (26048)------------------------------
% 2.16/0.64  % (26048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.64  % (26048)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.64  
% 2.16/0.64  % (26048)Memory used [KB]: 1535
% 2.16/0.64  % (26048)Time elapsed: 0.212 s
% 2.16/0.64  % (26048)------------------------------
% 2.16/0.64  % (26048)------------------------------
% 2.16/0.69  % (26041)Refutation found. Thanks to Tanya!
% 2.16/0.69  % SZS status Theorem for theBenchmark
% 2.16/0.70  % SZS output start Proof for theBenchmark
% 2.16/0.70  fof(f1992,plain,(
% 2.16/0.70    $false),
% 2.16/0.70    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f77,f152,f157,f243,f255,f260,f265,f270,f286,f355,f360,f365,f423,f428,f508,f806,f926,f1372,f1377,f1382,f1387,f1396,f1401,f1406,f1580,f1585,f1591,f1761,f1766,f1971,f1991])).
% 2.16/0.70  fof(f1991,plain,(
% 2.16/0.70    spl3_14 | ~spl3_31),
% 2.16/0.70    inference(avatar_contradiction_clause,[],[f1990])).
% 2.16/0.70  fof(f1990,plain,(
% 2.16/0.70    $false | (spl3_14 | ~spl3_31)),
% 2.16/0.70    inference(subsumption_resolution,[],[f1983,f354])).
% 2.16/0.70  fof(f354,plain,(
% 2.16/0.70    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) | spl3_14),
% 2.16/0.70    inference(avatar_component_clause,[],[f352])).
% 2.16/0.70  fof(f352,plain,(
% 2.16/0.70    spl3_14 <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.16/0.70  fof(f1983,plain,(
% 2.16/0.70    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) | ~spl3_31),
% 2.16/0.70    inference(superposition,[],[f61,f1760])).
% 2.16/0.70  fof(f1760,plain,(
% 2.16/0.70    k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | ~spl3_31),
% 2.16/0.70    inference(avatar_component_clause,[],[f1758])).
% 2.16/0.70  fof(f1758,plain,(
% 2.16/0.70    spl3_31 <=> k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.16/0.70  fof(f61,plain,(
% 2.16/0.70    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f30,f36])).
% 2.16/0.70  fof(f36,plain,(
% 2.16/0.70    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.16/0.70    inference(cnf_transformation,[],[f21])).
% 2.16/0.70  fof(f21,plain,(
% 2.16/0.70    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.16/0.70    inference(ennf_transformation,[],[f4])).
% 2.16/0.70  fof(f4,axiom,(
% 2.16/0.70    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.16/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.16/0.70  fof(f30,plain,(
% 2.16/0.70    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.16/0.70    inference(cnf_transformation,[],[f1])).
% 2.16/0.70  fof(f1,axiom,(
% 2.16/0.70    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.16/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.16/0.70  fof(f1971,plain,(
% 2.16/0.70    spl3_33 | ~spl3_25),
% 2.16/0.70    inference(avatar_split_clause,[],[f1960,f1393,f1968])).
% 2.16/0.70  fof(f1968,plain,(
% 2.16/0.70    spl3_33 <=> r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k2_xboole_0(sK2,sK2)))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 2.16/0.70  fof(f1393,plain,(
% 2.16/0.70    spl3_25 <=> k2_pre_topc(sK0,k2_xboole_0(sK2,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.16/0.70  fof(f1960,plain,(
% 2.16/0.70    r1_tarski(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k2_xboole_0(sK2,sK2))) | ~spl3_25),
% 2.16/0.70    inference(superposition,[],[f61,f1395])).
% 2.16/0.70  fof(f1395,plain,(
% 2.16/0.70    k2_pre_topc(sK0,k2_xboole_0(sK2,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2)) | ~spl3_25),
% 2.16/0.70    inference(avatar_component_clause,[],[f1393])).
% 2.16/0.70  fof(f1766,plain,(
% 2.16/0.70    spl3_32 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7),
% 2.16/0.70    inference(avatar_split_clause,[],[f226,f154,f149,f54,f49,f44,f39,f1763])).
% 2.16/0.70  fof(f1763,plain,(
% 2.16/0.70    spl3_32 <=> k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.16/0.70  fof(f39,plain,(
% 2.16/0.70    spl3_1 <=> v2_pre_topc(sK0)),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.16/0.70  fof(f44,plain,(
% 2.16/0.70    spl3_2 <=> l1_pre_topc(sK0)),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.16/0.70  fof(f49,plain,(
% 2.16/0.70    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.16/0.70  fof(f54,plain,(
% 2.16/0.70    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.16/0.70  fof(f149,plain,(
% 2.16/0.70    spl3_6 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.16/0.70  fof(f154,plain,(
% 2.16/0.70    spl3_7 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.16/0.70  fof(f226,plain,(
% 2.16/0.70    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7)),
% 2.16/0.70    inference(forward_demodulation,[],[f209,f94])).
% 2.16/0.70  fof(f94,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.16/0.70    inference(forward_demodulation,[],[f90,f85])).
% 2.16/0.70  fof(f85,plain,(
% 2.16/0.70    k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) | (~spl3_3 | ~spl3_4)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f56,f51,f37])).
% 2.16/0.70  fof(f37,plain,(
% 2.16/0.70    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.16/0.70    inference(cnf_transformation,[],[f23])).
% 2.16/0.70  fof(f23,plain,(
% 2.16/0.70    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.70    inference(flattening,[],[f22])).
% 2.16/0.70  fof(f22,plain,(
% 2.16/0.70    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.16/0.70    inference(ennf_transformation,[],[f6])).
% 2.16/0.70  fof(f6,axiom,(
% 2.16/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.16/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.16/0.70  fof(f51,plain,(
% 2.16/0.70    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.16/0.70    inference(avatar_component_clause,[],[f49])).
% 2.16/0.70  fof(f56,plain,(
% 2.16/0.70    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 2.16/0.70    inference(avatar_component_clause,[],[f54])).
% 2.16/0.70  fof(f90,plain,(
% 2.16/0.70    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f41,f46,f51,f56,f29])).
% 2.16/0.70  fof(f29,plain,(
% 2.16/0.70    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 2.16/0.70    inference(cnf_transformation,[],[f15])).
% 2.16/0.70  fof(f15,plain,(
% 2.16/0.70    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/0.70    inference(flattening,[],[f14])).
% 2.16/0.70  fof(f14,plain,(
% 2.16/0.70    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.16/0.70    inference(ennf_transformation,[],[f9])).
% 2.16/0.70  fof(f9,axiom,(
% 2.16/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))))),
% 2.16/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).
% 2.16/0.70  fof(f46,plain,(
% 2.16/0.70    l1_pre_topc(sK0) | ~spl3_2),
% 2.16/0.70    inference(avatar_component_clause,[],[f44])).
% 2.16/0.70  fof(f41,plain,(
% 2.16/0.70    v2_pre_topc(sK0) | ~spl3_1),
% 2.16/0.70    inference(avatar_component_clause,[],[f39])).
% 2.16/0.70  fof(f209,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) | (~spl3_6 | ~spl3_7)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f151,f156,f37])).
% 2.16/0.70  fof(f156,plain,(
% 2.16/0.70    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 2.16/0.70    inference(avatar_component_clause,[],[f154])).
% 2.16/0.70  fof(f151,plain,(
% 2.16/0.70    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 2.16/0.70    inference(avatar_component_clause,[],[f149])).
% 2.16/0.70  fof(f1761,plain,(
% 2.16/0.70    spl3_31 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7),
% 2.16/0.70    inference(avatar_split_clause,[],[f224,f154,f149,f54,f49,f44,f39,f1758])).
% 2.16/0.70  fof(f224,plain,(
% 2.16/0.70    k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_7)),
% 2.16/0.70    inference(forward_demodulation,[],[f215,f95])).
% 2.16/0.70  fof(f95,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.16/0.70    inference(forward_demodulation,[],[f89,f86])).
% 2.16/0.70  fof(f86,plain,(
% 2.16/0.70    k2_xboole_0(sK2,sK1) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) | (~spl3_3 | ~spl3_4)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f51,f56,f37])).
% 2.16/0.70  fof(f89,plain,(
% 2.16/0.70    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f41,f46,f56,f51,f29])).
% 2.16/0.70  fof(f215,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | (~spl3_6 | ~spl3_7)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f151,f156,f37])).
% 2.16/0.70  fof(f1591,plain,(
% 2.16/0.70    spl3_30 | ~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_7),
% 2.16/0.70    inference(avatar_split_clause,[],[f223,f154,f54,f44,f39,f1588])).
% 2.16/0.70  fof(f1588,plain,(
% 2.16/0.70    spl3_30 <=> k2_pre_topc(sK0,k2_xboole_0(sK1,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 2.16/0.70  fof(f223,plain,(
% 2.16/0.70    k2_pre_topc(sK0,k2_xboole_0(sK1,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_4 | ~spl3_7)),
% 2.16/0.70    inference(forward_demodulation,[],[f216,f93])).
% 2.16/0.70  fof(f93,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_4)),
% 2.16/0.70    inference(forward_demodulation,[],[f91,f87])).
% 2.16/0.70  fof(f87,plain,(
% 2.16/0.70    k2_xboole_0(sK1,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,sK1) | ~spl3_4),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f56,f56,f37])).
% 2.16/0.70  fof(f91,plain,(
% 2.16/0.70    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_2 | ~spl3_4)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f41,f46,f56,f56,f29])).
% 2.16/0.70  fof(f216,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl3_7),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f156,f156,f37])).
% 2.16/0.70  fof(f1585,plain,(
% 2.16/0.70    spl3_29 | ~spl3_3 | ~spl3_7),
% 2.16/0.70    inference(avatar_split_clause,[],[f218,f154,f49,f1582])).
% 2.16/0.70  fof(f1582,plain,(
% 2.16/0.70    spl3_29 <=> k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK2,k2_pre_topc(sK0,sK1))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.16/0.70  fof(f218,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK2,k2_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_7)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f51,f156,f37])).
% 2.16/0.70  fof(f1580,plain,(
% 2.16/0.70    spl3_28 | ~spl3_4 | ~spl3_7),
% 2.16/0.70    inference(avatar_split_clause,[],[f217,f154,f54,f1577])).
% 2.16/0.70  fof(f1577,plain,(
% 2.16/0.70    spl3_28 <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 2.16/0.70  fof(f217,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK1)) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_4 | ~spl3_7)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f56,f156,f37])).
% 2.16/0.70  fof(f1406,plain,(
% 2.16/0.70    spl3_27 | ~spl3_3 | ~spl3_7),
% 2.16/0.70    inference(avatar_split_clause,[],[f212,f154,f49,f1403])).
% 2.16/0.70  fof(f1403,plain,(
% 2.16/0.70    spl3_27 <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK2)),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 2.16/0.70  fof(f212,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK2) | (~spl3_3 | ~spl3_7)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f51,f156,f37])).
% 2.16/0.70  fof(f1401,plain,(
% 2.16/0.70    spl3_26 | ~spl3_4 | ~spl3_7),
% 2.16/0.70    inference(avatar_split_clause,[],[f211,f154,f54,f1398])).
% 2.16/0.70  fof(f1398,plain,(
% 2.16/0.70    spl3_26 <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.16/0.70  fof(f211,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) = k2_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_4 | ~spl3_7)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f56,f156,f37])).
% 2.16/0.70  fof(f1396,plain,(
% 2.16/0.70    spl3_25 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_6),
% 2.16/0.70    inference(avatar_split_clause,[],[f182,f149,f49,f44,f39,f1393])).
% 2.16/0.70  fof(f182,plain,(
% 2.16/0.70    k2_pre_topc(sK0,k2_xboole_0(sK2,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_6)),
% 2.16/0.70    inference(forward_demodulation,[],[f176,f96])).
% 2.16/0.70  fof(f96,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK2,sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 2.16/0.70    inference(forward_demodulation,[],[f88,f84])).
% 2.16/0.70  fof(f84,plain,(
% 2.16/0.70    k2_xboole_0(sK2,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,sK2) | ~spl3_3),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f51,f51,f37])).
% 2.16/0.70  fof(f88,plain,(
% 2.16/0.70    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_3)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f41,f46,f51,f51,f29])).
% 2.16/0.70  fof(f176,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2)) | ~spl3_6),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f151,f151,f37])).
% 2.16/0.70  fof(f1387,plain,(
% 2.16/0.70    spl3_24 | ~spl3_3 | ~spl3_6),
% 2.16/0.70    inference(avatar_split_clause,[],[f178,f149,f49,f1384])).
% 2.16/0.70  fof(f1384,plain,(
% 2.16/0.70    spl3_24 <=> k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK2)) = k2_xboole_0(sK2,k2_pre_topc(sK0,sK2))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.16/0.70  fof(f178,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK2)) = k2_xboole_0(sK2,k2_pre_topc(sK0,sK2)) | (~spl3_3 | ~spl3_6)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f51,f151,f37])).
% 2.16/0.70  fof(f1382,plain,(
% 2.16/0.70    spl3_23 | ~spl3_4 | ~spl3_6),
% 2.16/0.70    inference(avatar_split_clause,[],[f177,f149,f54,f1379])).
% 2.16/0.70  fof(f1379,plain,(
% 2.16/0.70    spl3_23 <=> k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK2))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.16/0.70  fof(f177,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) = k2_xboole_0(sK1,k2_pre_topc(sK0,sK2)) | (~spl3_4 | ~spl3_6)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f56,f151,f37])).
% 2.16/0.70  fof(f1377,plain,(
% 2.16/0.70    spl3_22 | ~spl3_3 | ~spl3_6),
% 2.16/0.70    inference(avatar_split_clause,[],[f173,f149,f49,f1374])).
% 2.16/0.70  fof(f1374,plain,(
% 2.16/0.70    spl3_22 <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK2) = k2_xboole_0(k2_pre_topc(sK0,sK2),sK2)),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.16/0.70  fof(f173,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK2) = k2_xboole_0(k2_pre_topc(sK0,sK2),sK2) | (~spl3_3 | ~spl3_6)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f51,f151,f37])).
% 2.16/0.70  fof(f1372,plain,(
% 2.16/0.70    spl3_21 | ~spl3_4 | ~spl3_6),
% 2.16/0.70    inference(avatar_split_clause,[],[f172,f149,f54,f1369])).
% 2.16/0.70  fof(f1369,plain,(
% 2.16/0.70    spl3_21 <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1) = k2_xboole_0(k2_pre_topc(sK0,sK2),sK1)),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.16/0.70  fof(f172,plain,(
% 2.16/0.70    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),sK1) = k2_xboole_0(k2_pre_topc(sK0,sK2),sK1) | (~spl3_4 | ~spl3_6)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f56,f151,f37])).
% 2.16/0.70  fof(f926,plain,(
% 2.16/0.70    spl3_20 | ~spl3_2 | ~spl3_7),
% 2.16/0.70    inference(avatar_split_clause,[],[f206,f154,f44,f923])).
% 2.16/0.70  fof(f923,plain,(
% 2.16/0.70    spl3_20 <=> m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.16/0.70  fof(f206,plain,(
% 2.16/0.70    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_7)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f46,f156,f32])).
% 2.16/0.70  fof(f32,plain,(
% 2.16/0.70    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.16/0.70    inference(cnf_transformation,[],[f17])).
% 2.16/0.70  fof(f17,plain,(
% 2.16/0.70    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.16/0.70    inference(flattening,[],[f16])).
% 2.16/0.70  fof(f16,plain,(
% 2.16/0.70    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.16/0.70    inference(ennf_transformation,[],[f8])).
% 2.16/0.70  fof(f8,axiom,(
% 2.16/0.70    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.16/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.16/0.70  fof(f806,plain,(
% 2.16/0.70    spl3_19 | ~spl3_2 | ~spl3_6),
% 2.16/0.70    inference(avatar_split_clause,[],[f168,f149,f44,f803])).
% 2.16/0.70  fof(f803,plain,(
% 2.16/0.70    spl3_19 <=> m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.16/0.70  fof(f168,plain,(
% 2.16/0.70    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_6)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f46,f151,f32])).
% 2.16/0.70  fof(f508,plain,(
% 2.16/0.70    ~spl3_7 | ~spl3_8 | spl3_5),
% 2.16/0.70    inference(avatar_split_clause,[],[f81,f74,f240,f154])).
% 2.16/0.70  fof(f240,plain,(
% 2.16/0.70    spl3_8 <=> r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.16/0.70  fof(f74,plain,(
% 2.16/0.70    spl3_5 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.16/0.70  fof(f81,plain,(
% 2.16/0.70    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 2.16/0.70    inference(superposition,[],[f76,f34])).
% 2.16/0.70  fof(f34,plain,(
% 2.16/0.70    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.16/0.70    inference(cnf_transformation,[],[f19])).
% 2.16/0.70  fof(f19,plain,(
% 2.16/0.70    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.70    inference(ennf_transformation,[],[f7])).
% 2.16/0.70  fof(f7,axiom,(
% 2.16/0.70    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.16/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.16/0.70  fof(f76,plain,(
% 2.16/0.70    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) | spl3_5),
% 2.16/0.70    inference(avatar_component_clause,[],[f74])).
% 2.16/0.70  fof(f428,plain,(
% 2.16/0.70    spl3_18 | ~spl3_1 | ~spl3_2 | ~spl3_3),
% 2.16/0.70    inference(avatar_split_clause,[],[f96,f49,f44,f39,f425])).
% 2.16/0.70  fof(f425,plain,(
% 2.16/0.70    spl3_18 <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK2,sK2))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.16/0.70  fof(f423,plain,(
% 2.16/0.70    spl3_17 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 2.16/0.70    inference(avatar_split_clause,[],[f95,f54,f49,f44,f39,f420])).
% 2.16/0.70  fof(f420,plain,(
% 2.16/0.70    spl3_17 <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.16/0.70  fof(f365,plain,(
% 2.16/0.70    spl3_16 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 2.16/0.70    inference(avatar_split_clause,[],[f94,f54,f49,f44,f39,f362])).
% 2.16/0.70  fof(f362,plain,(
% 2.16/0.70    spl3_16 <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.16/0.70  fof(f360,plain,(
% 2.16/0.70    spl3_15 | ~spl3_1 | ~spl3_2 | ~spl3_4),
% 2.16/0.70    inference(avatar_split_clause,[],[f93,f54,f44,f39,f357])).
% 2.16/0.70  fof(f357,plain,(
% 2.16/0.70    spl3_15 <=> k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK1))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.16/0.70  fof(f355,plain,(
% 2.16/0.70    ~spl3_14 | ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_13),
% 2.16/0.70    inference(avatar_split_clause,[],[f333,f283,f149,f54,f49,f44,f39,f352])).
% 2.16/0.70  fof(f283,plain,(
% 2.16/0.70    spl3_13 <=> r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))))),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.16/0.70  fof(f333,plain,(
% 2.16/0.70    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_13)),
% 2.16/0.70    inference(forward_demodulation,[],[f332,f31])).
% 2.16/0.70  fof(f31,plain,(
% 2.16/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.16/0.70    inference(cnf_transformation,[],[f2])).
% 2.16/0.70  fof(f2,axiom,(
% 2.16/0.70    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.16/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.16/0.70  fof(f332,plain,(
% 2.16/0.70    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_13)),
% 2.16/0.70    inference(backward_demodulation,[],[f285,f331])).
% 2.16/0.70  fof(f331,plain,(
% 2.16/0.70    ( ! [X0] : (k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_6)),
% 2.16/0.70    inference(forward_demodulation,[],[f321,f119])).
% 2.16/0.70  fof(f119,plain,(
% 2.16/0.70    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.16/0.70    inference(forward_demodulation,[],[f98,f108])).
% 2.16/0.70  fof(f108,plain,(
% 2.16/0.70    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) ) | (~spl3_3 | ~spl3_4)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f51,f71,f37])).
% 2.16/0.70  fof(f71,plain,(
% 2.16/0.70    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_4),
% 2.16/0.70    inference(backward_demodulation,[],[f65,f67])).
% 2.16/0.70  fof(f67,plain,(
% 2.16/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl3_4),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f56,f34])).
% 2.16/0.70  fof(f65,plain,(
% 2.16/0.70    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_4),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f56,f33])).
% 2.16/0.70  fof(f33,plain,(
% 2.16/0.70    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.16/0.70    inference(cnf_transformation,[],[f18])).
% 2.16/0.70  fof(f18,plain,(
% 2.16/0.70    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.70    inference(ennf_transformation,[],[f5])).
% 2.16/0.70  fof(f5,axiom,(
% 2.16/0.70    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.16/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 2.16/0.70  fof(f98,plain,(
% 2.16/0.70    ( ! [X0] : (k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0))) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) ) | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f46,f41,f51,f71,f29])).
% 2.16/0.70  fof(f321,plain,(
% 2.16/0.70    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) ) | (~spl3_2 | ~spl3_4 | ~spl3_6)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f151,f104,f37])).
% 2.16/0.70  fof(f104,plain,(
% 2.16/0.70    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X0)),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_2 | ~spl3_4)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f46,f71,f32])).
% 2.16/0.70  fof(f285,plain,(
% 2.16/0.70    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))) | spl3_13),
% 2.16/0.70    inference(avatar_component_clause,[],[f283])).
% 2.16/0.70  fof(f286,plain,(
% 2.16/0.70    ~spl3_13 | spl3_8),
% 2.16/0.70    inference(avatar_split_clause,[],[f244,f240,f283])).
% 2.16/0.70  fof(f244,plain,(
% 2.16/0.70    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))) | spl3_8),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f242,f35])).
% 2.16/0.70  fof(f35,plain,(
% 2.16/0.70    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.16/0.70    inference(cnf_transformation,[],[f20])).
% 2.16/0.70  fof(f20,plain,(
% 2.16/0.70    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.16/0.70    inference(ennf_transformation,[],[f3])).
% 2.16/0.70  fof(f3,axiom,(
% 2.16/0.70    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.16/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.16/0.70  fof(f242,plain,(
% 2.16/0.70    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) | spl3_8),
% 2.16/0.70    inference(avatar_component_clause,[],[f240])).
% 2.16/0.70  fof(f270,plain,(
% 2.16/0.70    spl3_12 | ~spl3_4),
% 2.16/0.70    inference(avatar_split_clause,[],[f87,f54,f267])).
% 2.16/0.70  fof(f267,plain,(
% 2.16/0.70    spl3_12 <=> k2_xboole_0(sK1,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,sK1)),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.16/0.70  fof(f265,plain,(
% 2.16/0.70    spl3_11 | ~spl3_3 | ~spl3_4),
% 2.16/0.70    inference(avatar_split_clause,[],[f86,f54,f49,f262])).
% 2.16/0.70  fof(f262,plain,(
% 2.16/0.70    spl3_11 <=> k2_xboole_0(sK2,sK1) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.16/0.70  fof(f260,plain,(
% 2.16/0.70    spl3_10 | ~spl3_3 | ~spl3_4),
% 2.16/0.70    inference(avatar_split_clause,[],[f85,f54,f49,f257])).
% 2.16/0.70  fof(f257,plain,(
% 2.16/0.70    spl3_10 <=> k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.16/0.70  fof(f255,plain,(
% 2.16/0.70    spl3_9 | ~spl3_3),
% 2.16/0.70    inference(avatar_split_clause,[],[f84,f49,f252])).
% 2.16/0.70  fof(f252,plain,(
% 2.16/0.70    spl3_9 <=> k2_xboole_0(sK2,sK2) = k4_subset_1(u1_struct_0(sK0),sK2,sK2)),
% 2.16/0.70    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.16/0.70  fof(f243,plain,(
% 2.16/0.70    ~spl3_8 | spl3_5 | ~spl3_7),
% 2.16/0.70    inference(avatar_split_clause,[],[f222,f154,f74,f240])).
% 2.16/0.70  fof(f222,plain,(
% 2.16/0.70    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) | (spl3_5 | ~spl3_7)),
% 2.16/0.70    inference(backward_demodulation,[],[f76,f219])).
% 2.16/0.70  fof(f219,plain,(
% 2.16/0.70    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) ) | ~spl3_7),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f156,f34])).
% 2.16/0.70  fof(f157,plain,(
% 2.16/0.70    spl3_7 | ~spl3_2 | ~spl3_4),
% 2.16/0.70    inference(avatar_split_clause,[],[f83,f54,f44,f154])).
% 2.16/0.70  fof(f83,plain,(
% 2.16/0.70    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_4)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f46,f56,f32])).
% 2.16/0.70  fof(f152,plain,(
% 2.16/0.70    spl3_6 | ~spl3_2 | ~spl3_3),
% 2.16/0.70    inference(avatar_split_clause,[],[f82,f49,f44,f149])).
% 2.16/0.70  fof(f82,plain,(
% 2.16/0.70    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3)),
% 2.16/0.70    inference(unit_resulting_resolution,[],[f46,f51,f32])).
% 2.16/0.70  fof(f77,plain,(
% 2.16/0.70    ~spl3_5 | ~spl3_4),
% 2.16/0.70    inference(avatar_split_clause,[],[f70,f54,f74])).
% 2.16/0.70  fof(f70,plain,(
% 2.16/0.70    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_4),
% 2.16/0.70    inference(backward_demodulation,[],[f25,f67])).
% 2.16/0.70  fof(f25,plain,(
% 2.16/0.70    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 2.16/0.70    inference(cnf_transformation,[],[f13])).
% 2.16/0.70  fof(f13,plain,(
% 2.16/0.70    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.16/0.70    inference(flattening,[],[f12])).
% 2.16/0.70  fof(f12,plain,(
% 2.16/0.70    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.16/0.70    inference(ennf_transformation,[],[f11])).
% 2.16/0.70  fof(f11,negated_conjecture,(
% 2.16/0.70    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 2.16/0.70    inference(negated_conjecture,[],[f10])).
% 2.16/0.70  fof(f10,conjecture,(
% 2.16/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 2.16/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).
% 2.16/0.70  fof(f57,plain,(
% 2.16/0.70    spl3_4),
% 2.16/0.70    inference(avatar_split_clause,[],[f26,f54])).
% 2.16/0.70  fof(f26,plain,(
% 2.16/0.70    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.16/0.70    inference(cnf_transformation,[],[f13])).
% 2.16/0.70  fof(f52,plain,(
% 2.16/0.70    spl3_3),
% 2.16/0.70    inference(avatar_split_clause,[],[f24,f49])).
% 2.16/0.70  fof(f24,plain,(
% 2.16/0.70    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.16/0.70    inference(cnf_transformation,[],[f13])).
% 2.16/0.70  fof(f47,plain,(
% 2.16/0.70    spl3_2),
% 2.16/0.70    inference(avatar_split_clause,[],[f28,f44])).
% 2.16/0.70  fof(f28,plain,(
% 2.16/0.70    l1_pre_topc(sK0)),
% 2.16/0.70    inference(cnf_transformation,[],[f13])).
% 2.16/0.70  fof(f42,plain,(
% 2.16/0.70    spl3_1),
% 2.16/0.70    inference(avatar_split_clause,[],[f27,f39])).
% 2.16/0.70  fof(f27,plain,(
% 2.16/0.70    v2_pre_topc(sK0)),
% 2.16/0.70    inference(cnf_transformation,[],[f13])).
% 2.16/0.70  % SZS output end Proof for theBenchmark
% 2.16/0.70  % (26041)------------------------------
% 2.16/0.70  % (26041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.70  % (26041)Termination reason: Refutation
% 2.16/0.70  
% 2.16/0.70  % (26041)Memory used [KB]: 3454
% 2.16/0.70  % (26041)Time elapsed: 0.226 s
% 2.16/0.70  % (26041)------------------------------
% 2.16/0.70  % (26041)------------------------------
% 2.60/0.70  % (26025)Success in time 0.346 s
%------------------------------------------------------------------------------
