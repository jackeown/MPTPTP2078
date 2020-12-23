%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 369 expanded)
%              Number of leaves         :   46 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  956 (1941 expanded)
%              Number of equality atoms :   40 ( 138 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f525,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f86,f90,f94,f98,f102,f106,f114,f118,f122,f126,f138,f142,f150,f163,f167,f171,f188,f198,f202,f206,f210,f214,f224,f238,f265,f269,f276,f290,f450,f498,f510,f517,f524])).

fof(f524,plain,
    ( spl6_8
    | ~ spl6_12
    | ~ spl6_62 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | spl6_8
    | ~ spl6_12
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f521,f97])).

fof(f97,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_8
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f521,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl6_12
    | ~ spl6_62 ),
    inference(resolution,[],[f506,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl6_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f506,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f505])).

fof(f505,plain,
    ( spl6_62
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f517,plain,
    ( spl6_9
    | ~ spl6_12
    | ~ spl6_63 ),
    inference(avatar_contradiction_clause,[],[f516])).

fof(f516,plain,
    ( $false
    | spl6_9
    | ~ spl6_12
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f514,f101])).

fof(f101,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f514,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl6_12
    | ~ spl6_63 ),
    inference(resolution,[],[f509,f113])).

fof(f509,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl6_63
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f510,plain,
    ( spl6_62
    | spl6_63
    | ~ spl6_25
    | ~ spl6_61 ),
    inference(avatar_split_clause,[],[f499,f496,f165,f508,f505])).

fof(f165,plain,
    ( spl6_25
  <=> ! [X1,X3,X0] :
        ( r2_hidden(X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f496,plain,
    ( spl6_61
  <=> r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f499,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl6_25
    | ~ spl6_61 ),
    inference(resolution,[],[f497,f166])).

fof(f166,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
        | r2_hidden(X3,X1)
        | r2_hidden(X3,X0) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f165])).

fof(f497,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f496])).

fof(f498,plain,
    ( spl6_61
    | spl6_1
    | ~ spl6_6
    | ~ spl6_20
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f460,f448,f145,f88,f68,f496])).

fof(f68,plain,
    ( spl6_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f88,plain,
    ( spl6_6
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f145,plain,
    ( spl6_20
  <=> r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f448,plain,
    ( spl6_58
  <=> ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f460,plain,
    ( r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl6_1
    | ~ spl6_6
    | ~ spl6_20
    | ~ spl6_58 ),
    inference(backward_demodulation,[],[f146,f458])).

fof(f458,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl6_1
    | ~ spl6_6
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f455,f69])).

fof(f69,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f455,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl6_6
    | ~ spl6_58 ),
    inference(resolution,[],[f449,f89])).

fof(f89,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f449,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)) )
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f448])).

fof(f146,plain,
    ( r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f145])).

fof(f450,plain,
    ( spl6_58
    | spl6_2
    | ~ spl6_7
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f295,f288,f92,f72,f448])).

fof(f72,plain,
    ( spl6_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f92,plain,
    ( spl6_7
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f288,plain,
    ( spl6_42
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f295,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)) )
    | spl6_2
    | ~ spl6_7
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f292,f73])).

fof(f73,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f292,plain,
    ( ! [X1] :
        ( v2_struct_0(sK1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)) )
    | ~ spl6_7
    | ~ spl6_42 ),
    inference(resolution,[],[f289,f93])).

fof(f93,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f289,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f288])).

fof(f290,plain,
    ( spl6_42
    | spl6_3
    | ~ spl6_5
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f282,f274,f84,f76,f288])).

fof(f76,plain,
    ( spl6_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f84,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f274,plain,
    ( spl6_40
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f282,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl6_3
    | ~ spl6_5
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f280,f77])).

fof(f77,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f280,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | ~ spl6_5
    | ~ spl6_40 ),
    inference(resolution,[],[f275,f85])).

fof(f85,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f275,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f274])).

fof(f276,plain,
    ( spl6_40
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f272,f267,f208,f204,f196,f274])).

fof(f196,plain,
    ( spl6_32
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f204,plain,
    ( spl6_34
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v1_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f208,plain,
    ( spl6_35
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f267,plain,
    ( spl6_39
  <=> ! [X1,X0,X2] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(k1_tsep_1(X0,X1,X2))
        | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
        | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f272,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) )
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_35
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f271,f209])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f208])).

fof(f271,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) )
    | ~ spl6_32
    | ~ spl6_34
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f270,f205])).

fof(f205,plain,
    ( ! [X2,X0,X1] :
        ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f204])).

fof(f270,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
        | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) )
    | ~ spl6_32
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f268,f197])).

fof(f197,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X0) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f196])).

fof(f268,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(k1_tsep_1(X0,X1,X2))
        | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
        | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) )
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f267])).

fof(f269,plain,(
    spl6_39 ),
    inference(avatar_split_clause,[],[f63,f267])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f265,plain,
    ( spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_35
    | ~ spl6_36 ),
    inference(avatar_contradiction_clause,[],[f264])).

% (339)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f264,plain,
    ( $false
    | spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f263,f77])).

fof(f263,plain,
    ( v2_struct_0(sK0)
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f262,f89])).

fof(f262,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f261,f69])).

fof(f261,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f260,f93])).

fof(f260,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f259,f73])).

fof(f259,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f258,f81])).

fof(f81,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f258,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_35
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f257,f85])).

fof(f257,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_35
    | ~ spl6_36 ),
    inference(duplicate_literal_removal,[],[f256])).

fof(f256,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_35
    | ~ spl6_36 ),
    inference(resolution,[],[f213,f209])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl6_36
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f238,plain,
    ( spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f236,f77])).

fof(f236,plain,
    ( v2_struct_0(sK0)
    | spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f235,f89])).

fof(f235,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f234,f69])).

fof(f234,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f233,f93])).

fof(f233,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl6_2
    | ~ spl6_5
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f232,f73])).

fof(f232,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f230,f85])).

fof(f230,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_28
    | ~ spl6_32 ),
    inference(resolution,[],[f181,f197])).

fof(f181,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl6_28
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f224,plain,
    ( spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | spl6_1
    | spl6_2
    | spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f222,f77])).

fof(f222,plain,
    ( v2_struct_0(sK0)
    | spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f221,f89])).

fof(f221,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl6_1
    | spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f220,f69])).

fof(f220,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl6_2
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f219,f93])).

fof(f219,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl6_2
    | ~ spl6_5
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f218,f73])).

fof(f218,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_5
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f217,f85])).

fof(f217,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(resolution,[],[f201,f209])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_33
  <=> ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f214,plain,
    ( spl6_36
    | ~ spl6_19
    | spl6_30 ),
    inference(avatar_split_clause,[],[f194,f186,f140,f212])).

fof(f140,plain,
    ( spl6_19
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f186,plain,
    ( spl6_30
  <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_19
    | spl6_30 ),
    inference(resolution,[],[f187,f141])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f140])).

fof(f187,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl6_30 ),
    inference(avatar_component_clause,[],[f186])).

fof(f210,plain,(
    spl6_35 ),
    inference(avatar_split_clause,[],[f54,f208])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f206,plain,(
    spl6_34 ),
    inference(avatar_split_clause,[],[f53,f204])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v1_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f202,plain,
    ( spl6_33
    | ~ spl6_13
    | spl6_29 ),
    inference(avatar_split_clause,[],[f193,f183,f116,f200])).

fof(f116,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f183,plain,
    ( spl6_29
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_13
    | spl6_29 ),
    inference(resolution,[],[f184,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f116])).

% (356)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f184,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f183])).

fof(f198,plain,(
    spl6_32 ),
    inference(avatar_split_clause,[],[f52,f196])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f188,plain,
    ( spl6_28
    | ~ spl6_29
    | ~ spl6_30
    | ~ spl6_18
    | ~ spl6_24
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f174,f169,f161,f136,f186,f183,f180])).

fof(f136,plain,
    ( spl6_18
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_xboole_0(sK4(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f161,plain,
    ( spl6_24
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f169,plain,
    ( spl6_26
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f174,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl6_18
    | ~ spl6_24
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f172,f137])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK4(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f136])).

fof(f172,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v1_xboole_0(sK4(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl6_24
    | ~ spl6_26 ),
    inference(resolution,[],[f170,f162])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(X0) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f161])).

fof(f170,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,(
    spl6_26 ),
    inference(avatar_split_clause,[],[f42,f169])).

fof(f42,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f167,plain,(
    spl6_25 ),
    inference(avatar_split_clause,[],[f66,f165])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f163,plain,
    ( spl6_24
    | ~ spl6_14
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f155,f148,f120,f161])).

fof(f120,plain,
    ( spl6_14
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f148,plain,
    ( spl6_21
  <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
        | v1_xboole_0(X0) )
    | ~ spl6_14
    | ~ spl6_21 ),
    inference(resolution,[],[f149,f121])).

fof(f121,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f149,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f148])).

fof(f150,plain,
    ( spl6_20
    | spl6_21
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f143,f124,f104,f148,f145])).

fof(f104,plain,
    ( spl6_10
  <=> m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f124,plain,
    ( spl6_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f143,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(resolution,[],[f125,f105])).

fof(f105,plain,
    ( m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f124])).

fof(f142,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f48,f140])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f138,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f43,f136])).

fof(f43,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f126,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f51,f124])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f122,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f41,f120])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f118,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f40,f116])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f114,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f50,f112])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f106,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f32,f104])).

fof(f32,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
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
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(rectify,[],[f12])).

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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X1))
                           => X3 != X4 ) ) ) ) ) ) ),
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
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ~ ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X2))
                         => X3 != X4 )
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => X3 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).

fof(f102,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f62,f100])).

fof(f62,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f98,plain,(
    ~ spl6_8 ),
    inference(avatar_split_clause,[],[f61,f96])).

fof(f61,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f36,f92])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f39,f84])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f82,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f38,f80])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f78,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f37,f76])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f74,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f35,f72])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:57:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (344)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (348)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (347)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (352)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (354)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (340)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (345)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (346)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (340)Refutation not found, incomplete strategy% (340)------------------------------
% 0.22/0.48  % (340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (340)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (340)Memory used [KB]: 10618
% 0.22/0.48  % (340)Time elapsed: 0.077 s
% 0.22/0.48  % (340)------------------------------
% 0.22/0.48  % (340)------------------------------
% 0.22/0.48  % (342)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (357)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (341)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (353)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (343)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (350)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (348)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f525,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f86,f90,f94,f98,f102,f106,f114,f118,f122,f126,f138,f142,f150,f163,f167,f171,f188,f198,f202,f206,f210,f214,f224,f238,f265,f269,f276,f290,f450,f498,f510,f517,f524])).
% 0.22/0.50  fof(f524,plain,(
% 0.22/0.50    spl6_8 | ~spl6_12 | ~spl6_62),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f523])).
% 0.22/0.50  fof(f523,plain,(
% 0.22/0.50    $false | (spl6_8 | ~spl6_12 | ~spl6_62)),
% 0.22/0.50    inference(subsumption_resolution,[],[f521,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,u1_struct_0(sK1)) | spl6_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl6_8 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.50  fof(f521,plain,(
% 0.22/0.50    m1_subset_1(sK3,u1_struct_0(sK1)) | (~spl6_12 | ~spl6_62)),
% 0.22/0.50    inference(resolution,[],[f506,f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) ) | ~spl6_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f112])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl6_12 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.50  fof(f506,plain,(
% 0.22/0.50    r2_hidden(sK3,u1_struct_0(sK1)) | ~spl6_62),
% 0.22/0.50    inference(avatar_component_clause,[],[f505])).
% 0.22/0.50  fof(f505,plain,(
% 0.22/0.50    spl6_62 <=> r2_hidden(sK3,u1_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 0.22/0.50  fof(f517,plain,(
% 0.22/0.50    spl6_9 | ~spl6_12 | ~spl6_63),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f516])).
% 0.22/0.50  fof(f516,plain,(
% 0.22/0.50    $false | (spl6_9 | ~spl6_12 | ~spl6_63)),
% 0.22/0.50    inference(subsumption_resolution,[],[f514,f101])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl6_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    spl6_9 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.50  fof(f514,plain,(
% 0.22/0.50    m1_subset_1(sK3,u1_struct_0(sK2)) | (~spl6_12 | ~spl6_63)),
% 0.22/0.50    inference(resolution,[],[f509,f113])).
% 0.22/0.50  fof(f509,plain,(
% 0.22/0.50    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl6_63),
% 0.22/0.50    inference(avatar_component_clause,[],[f508])).
% 0.22/0.50  fof(f508,plain,(
% 0.22/0.50    spl6_63 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 0.22/0.50  fof(f510,plain,(
% 0.22/0.50    spl6_62 | spl6_63 | ~spl6_25 | ~spl6_61),
% 0.22/0.50    inference(avatar_split_clause,[],[f499,f496,f165,f508,f505])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    spl6_25 <=> ! [X1,X3,X0] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.50  fof(f496,plain,(
% 0.22/0.50    spl6_61 <=> r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 0.22/0.50  fof(f499,plain,(
% 0.22/0.50    r2_hidden(sK3,u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK1)) | (~spl6_25 | ~spl6_61)),
% 0.22/0.50    inference(resolution,[],[f497,f166])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) ) | ~spl6_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f165])).
% 0.22/0.50  fof(f497,plain,(
% 0.22/0.50    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | ~spl6_61),
% 0.22/0.50    inference(avatar_component_clause,[],[f496])).
% 0.22/0.50  fof(f498,plain,(
% 0.22/0.50    spl6_61 | spl6_1 | ~spl6_6 | ~spl6_20 | ~spl6_58),
% 0.22/0.50    inference(avatar_split_clause,[],[f460,f448,f145,f88,f68,f496])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl6_1 <=> v2_struct_0(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl6_6 <=> m1_pre_topc(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    spl6_20 <=> r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.50  fof(f448,plain,(
% 0.22/0.50    spl6_58 <=> ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.22/0.50  fof(f460,plain,(
% 0.22/0.50    r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) | (spl6_1 | ~spl6_6 | ~spl6_20 | ~spl6_58)),
% 0.22/0.50    inference(backward_demodulation,[],[f146,f458])).
% 0.22/0.50  fof(f458,plain,(
% 0.22/0.50    u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl6_1 | ~spl6_6 | ~spl6_58)),
% 0.22/0.50    inference(subsumption_resolution,[],[f455,f69])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ~v2_struct_0(sK2) | spl6_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f68])).
% 0.22/0.50  fof(f455,plain,(
% 0.22/0.50    v2_struct_0(sK2) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (~spl6_6 | ~spl6_58)),
% 0.22/0.50    inference(resolution,[],[f449,f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK0) | ~spl6_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f88])).
% 0.22/0.50  fof(f449,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1))) ) | ~spl6_58),
% 0.22/0.50    inference(avatar_component_clause,[],[f448])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl6_20),
% 0.22/0.50    inference(avatar_component_clause,[],[f145])).
% 0.22/0.50  fof(f450,plain,(
% 0.22/0.50    spl6_58 | spl6_2 | ~spl6_7 | ~spl6_42),
% 0.22/0.50    inference(avatar_split_clause,[],[f295,f288,f92,f72,f448])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl6_2 <=> v2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl6_7 <=> m1_pre_topc(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    spl6_42 <=> ! [X1,X0] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.22/0.50  fof(f295,plain,(
% 0.22/0.50    ( ! [X1] : (v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1))) ) | (spl6_2 | ~spl6_7 | ~spl6_42)),
% 0.22/0.50    inference(subsumption_resolution,[],[f292,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ~v2_struct_0(sK1) | spl6_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f72])).
% 0.22/0.50  fof(f292,plain,(
% 0.22/0.50    ( ! [X1] : (v2_struct_0(sK1) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1))) ) | (~spl6_7 | ~spl6_42)),
% 0.22/0.50    inference(resolution,[],[f289,f93])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK0) | ~spl6_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f92])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1))) ) | ~spl6_42),
% 0.22/0.50    inference(avatar_component_clause,[],[f288])).
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    spl6_42 | spl6_3 | ~spl6_5 | ~spl6_40),
% 0.22/0.50    inference(avatar_split_clause,[],[f282,f274,f84,f76,f288])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl6_3 <=> v2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl6_5 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.50  fof(f274,plain,(
% 0.22/0.50    spl6_40 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1))) ) | (spl6_3 | ~spl6_5 | ~spl6_40)),
% 0.22/0.50    inference(subsumption_resolution,[],[f280,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ~v2_struct_0(sK0) | spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f76])).
% 0.22/0.50  fof(f280,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1))) ) | (~spl6_5 | ~spl6_40)),
% 0.22/0.50    inference(resolution,[],[f275,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl6_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f84])).
% 0.22/0.50  fof(f275,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) ) | ~spl6_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f274])).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    spl6_40 | ~spl6_32 | ~spl6_34 | ~spl6_35 | ~spl6_39),
% 0.22/0.50    inference(avatar_split_clause,[],[f272,f267,f208,f204,f196,f274])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    spl6_32 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v2_struct_0(k1_tsep_1(X0,X1,X2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    spl6_34 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v1_pre_topc(k1_tsep_1(X0,X1,X2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    spl6_35 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    spl6_39 <=> ! [X1,X0,X2] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.22/0.50  fof(f272,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) ) | (~spl6_32 | ~spl6_34 | ~spl6_35 | ~spl6_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f271,f209])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) ) | ~spl6_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f208])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) ) | (~spl6_32 | ~spl6_34 | ~spl6_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f270,f205])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) ) | ~spl6_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f204])).
% 0.22/0.50  fof(f270,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) ) | (~spl6_32 | ~spl6_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f268,f197])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) ) | ~spl6_32),
% 0.22/0.50    inference(avatar_component_clause,[],[f196])).
% 0.22/0.50  fof(f268,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) ) | ~spl6_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f267])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    spl6_39),
% 0.22/0.50    inference(avatar_split_clause,[],[f63,f267])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 0.22/0.50    inference(equality_resolution,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 0.22/0.50  fof(f265,plain,(
% 0.22/0.50    spl6_1 | spl6_2 | spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_35 | ~spl6_36),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f264])).
% 0.22/0.50  % (339)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    $false | (spl6_1 | spl6_2 | spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_35 | ~spl6_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f263,f77])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    v2_struct_0(sK0) | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_35 | ~spl6_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f262,f89])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_35 | ~spl6_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f261,f69])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_35 | ~spl6_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f260,f93])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_35 | ~spl6_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f259,f73])).
% 0.22/0.50  fof(f259,plain,(
% 0.22/0.50    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl6_4 | ~spl6_5 | ~spl6_35 | ~spl6_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f258,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    v2_pre_topc(sK0) | ~spl6_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl6_4 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.50  fof(f258,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_35 | ~spl6_36)),
% 0.22/0.50    inference(subsumption_resolution,[],[f257,f85])).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl6_35 | ~spl6_36)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f256])).
% 0.22/0.50  fof(f256,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl6_35 | ~spl6_36)),
% 0.22/0.50    inference(resolution,[],[f213,f209])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl6_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f212])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    spl6_36 <=> ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    spl6_1 | spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_28 | ~spl6_32),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f237])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    $false | (spl6_1 | spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_28 | ~spl6_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f236,f77])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    v2_struct_0(sK0) | (spl6_1 | spl6_2 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_28 | ~spl6_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f235,f89])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl6_1 | spl6_2 | ~spl6_5 | ~spl6_7 | ~spl6_28 | ~spl6_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f234,f69])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl6_2 | ~spl6_5 | ~spl6_7 | ~spl6_28 | ~spl6_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f233,f93])).
% 0.22/0.50  fof(f233,plain,(
% 0.22/0.50    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl6_2 | ~spl6_5 | ~spl6_28 | ~spl6_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f232,f73])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_28 | ~spl6_32)),
% 0.22/0.50    inference(subsumption_resolution,[],[f230,f85])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl6_28 | ~spl6_32)),
% 0.22/0.50    inference(resolution,[],[f181,f197])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~spl6_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f180])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    spl6_28 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    spl6_1 | spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_33 | ~spl6_35),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f223])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    $false | (spl6_1 | spl6_2 | spl6_3 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_33 | ~spl6_35)),
% 0.22/0.50    inference(subsumption_resolution,[],[f222,f77])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    v2_struct_0(sK0) | (spl6_1 | spl6_2 | ~spl6_5 | ~spl6_6 | ~spl6_7 | ~spl6_33 | ~spl6_35)),
% 0.22/0.50    inference(subsumption_resolution,[],[f221,f89])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl6_1 | spl6_2 | ~spl6_5 | ~spl6_7 | ~spl6_33 | ~spl6_35)),
% 0.22/0.50    inference(subsumption_resolution,[],[f220,f69])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl6_2 | ~spl6_5 | ~spl6_7 | ~spl6_33 | ~spl6_35)),
% 0.22/0.50    inference(subsumption_resolution,[],[f219,f93])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl6_2 | ~spl6_5 | ~spl6_33 | ~spl6_35)),
% 0.22/0.50    inference(subsumption_resolution,[],[f218,f73])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl6_5 | ~spl6_33 | ~spl6_35)),
% 0.22/0.50    inference(subsumption_resolution,[],[f217,f85])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl6_33 | ~spl6_35)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f216])).
% 0.22/0.50  fof(f216,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl6_33 | ~spl6_35)),
% 0.22/0.50    inference(resolution,[],[f201,f209])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0)) ) | ~spl6_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f200])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    spl6_33 <=> ! [X0] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    spl6_36 | ~spl6_19 | spl6_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f194,f186,f140,f212])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl6_19 <=> ! [X1,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    spl6_30 <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) | ~v2_pre_topc(X0)) ) | (~spl6_19 | spl6_30)),
% 0.22/0.50    inference(resolution,[],[f187,f141])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0)) ) | ~spl6_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f140])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl6_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f186])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    spl6_35),
% 0.22/0.50    inference(avatar_split_clause,[],[f54,f208])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    spl6_34),
% 0.22/0.50    inference(avatar_split_clause,[],[f53,f204])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v1_pre_topc(k1_tsep_1(X0,X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    spl6_33 | ~spl6_13 | spl6_29),
% 0.22/0.50    inference(avatar_split_clause,[],[f193,f183,f116,f200])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl6_13 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    spl6_29 <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.22/0.50  fof(f193,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0)) ) | (~spl6_13 | spl6_29)),
% 0.22/0.50    inference(resolution,[],[f184,f117])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl6_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f116])).
% 0.22/0.50  % (356)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | spl6_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f183])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    spl6_32),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f196])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~v2_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    spl6_28 | ~spl6_29 | ~spl6_30 | ~spl6_18 | ~spl6_24 | ~spl6_26),
% 0.22/0.50    inference(avatar_split_clause,[],[f174,f169,f161,f136,f186,f183,f180])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl6_18 <=> ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(sK4(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl6_24 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) | v1_xboole_0(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    spl6_26 <=> ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | (~spl6_18 | ~spl6_24 | ~spl6_26)),
% 0.22/0.50    inference(subsumption_resolution,[],[f172,f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(sK4(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f136])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | v1_xboole_0(sK4(k1_tsep_1(sK0,sK1,sK2))) | (~spl6_24 | ~spl6_26)),
% 0.22/0.50    inference(resolution,[],[f170,f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) | v1_xboole_0(X0)) ) | ~spl6_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl6_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f169])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    spl6_26),
% 0.22/0.50    inference(avatar_split_clause,[],[f42,f169])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_tops_1)).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    spl6_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f66,f165])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl6_24 | ~spl6_14 | ~spl6_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f155,f148,f120,f161])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl6_14 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    spl6_21 <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) | v1_xboole_0(X0)) ) | (~spl6_14 | ~spl6_21)),
% 0.22/0.50    inference(resolution,[],[f149,f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) ) | ~spl6_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f120])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl6_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f148])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    spl6_20 | spl6_21 | ~spl6_10 | ~spl6_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f143,f124,f104,f148,f145])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    spl6_10 <=> m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    spl6_15 <=> ! [X1,X0] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | (~spl6_10 | ~spl6_15)),
% 0.22/0.50    inference(resolution,[],[f125,f105])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl6_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f104])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) ) | ~spl6_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f124])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl6_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f48,f140])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl6_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f43,f136])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(sK4(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    spl6_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f51,f124])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    spl6_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f120])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    spl6_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f116])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    spl6_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f112])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    spl6_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f104])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 0.22/0.50    inference(rectify,[],[f12])).
% 0.22/0.50  fof(f12,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f11])).
% 0.22/0.50  fof(f11,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tmap_1)).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    ~spl6_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f62,f100])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.22/0.50    inference(equality_resolution,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ~spl6_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f61,f96])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.22/0.50    inference(equality_resolution,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK1)) | sK3 != X5) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    spl6_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f92])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    m1_pre_topc(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f88])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    m1_pre_topc(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl6_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f84])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f80])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ~spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f76])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ~spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f35,f72])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ~v2_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ~spl6_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f68])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ~v2_struct_0(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (348)------------------------------
% 0.22/0.50  % (348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (348)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (348)Memory used [KB]: 10874
% 0.22/0.50  % (348)Time elapsed: 0.094 s
% 0.22/0.50  % (348)------------------------------
% 0.22/0.50  % (348)------------------------------
% 0.22/0.50  % (338)Success in time 0.136 s
%------------------------------------------------------------------------------
