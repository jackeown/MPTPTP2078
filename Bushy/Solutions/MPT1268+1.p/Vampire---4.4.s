%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t86_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:33 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 322 expanded)
%              Number of leaves         :   27 ( 135 expanded)
%              Depth                    :   10
%              Number of atoms          :  503 (1164 expanded)
%              Number of equality atoms :   30 (  78 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1669,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f89,f93,f126,f134,f273,f277,f292,f326,f334,f342,f346,f394,f398,f489,f751,f1429,f1468,f1506,f1540,f1599,f1668])).

fof(f1668,plain,
    ( ~ spl6_62
    | spl6_77
    | ~ spl6_78
    | ~ spl6_102
    | ~ spl6_300 ),
    inference(avatar_contradiction_clause,[],[f1667])).

fof(f1667,plain,
    ( $false
    | ~ spl6_62
    | ~ spl6_77
    | ~ spl6_78
    | ~ spl6_102
    | ~ spl6_300 ),
    inference(subsumption_resolution,[],[f1666,f333])).

fof(f333,plain,
    ( k1_xboole_0 != sK2
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl6_77
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f1666,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_62
    | ~ spl6_78
    | ~ spl6_102
    | ~ spl6_300 ),
    inference(subsumption_resolution,[],[f1665,f290])).

fof(f290,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl6_62
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f1665,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | k1_xboole_0 = sK2
    | ~ spl6_78
    | ~ spl6_102
    | ~ spl6_300 ),
    inference(subsumption_resolution,[],[f1664,f341])).

fof(f341,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl6_78
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1664,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2,sK0)
    | k1_xboole_0 = sK2
    | ~ spl6_102
    | ~ spl6_300 ),
    inference(resolution,[],[f488,f1428])).

fof(f1428,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK2)
    | ~ spl6_300 ),
    inference(avatar_component_clause,[],[f1427])).

fof(f1427,plain,
    ( spl6_300
  <=> r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_300])])).

fof(f488,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f487])).

fof(f487,plain,
    ( spl6_102
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ v3_pre_topc(X0,sK0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f1599,plain,
    ( spl6_290
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f1589,f340,f124,f91,f1405])).

fof(f1405,plain,
    ( spl6_290
  <=> r1_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_290])])).

fof(f91,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f124,plain,
    ( spl6_10
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1589,plain,
    ( r1_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl6_4
    | ~ spl6_10
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f1581,f125])).

fof(f125,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f1581,plain,
    ( ~ r1_tarski(sK2,sK1)
    | r1_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl6_4
    | ~ spl6_78 ),
    inference(resolution,[],[f1570,f92])).

fof(f92,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f1570,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X1)
        | r1_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),X1)) )
    | ~ spl6_78 ),
    inference(resolution,[],[f341,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X2)
      | r1_xboole_0(X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t86_tops_1.p',t44_subset_1)).

fof(f1540,plain,
    ( spl6_8
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f281,f268,f91,f87,f336])).

fof(f336,plain,
    ( spl6_8
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f87,plain,
    ( spl6_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f268,plain,
    ( spl6_56
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f281,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f280,f88])).

fof(f88,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f280,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_1(sK1,sK0)
    | ~ spl6_4
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f279,f92])).

fof(f279,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_tops_1(sK1,sK0)
    | ~ spl6_56 ),
    inference(resolution,[],[f269,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t86_tops_1.p',d4_tops_1)).

fof(f269,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f268])).

fof(f1506,plain,
    ( ~ spl6_4
    | ~ spl6_74
    | spl6_83
    | ~ spl6_130 ),
    inference(avatar_contradiction_clause,[],[f1505])).

fof(f1505,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_74
    | ~ spl6_83
    | ~ spl6_130 ),
    inference(subsumption_resolution,[],[f1504,f325])).

fof(f325,plain,
    ( m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl6_74
  <=> m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f1504,plain,
    ( ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_83
    | ~ spl6_130 ),
    inference(subsumption_resolution,[],[f1503,f393])).

fof(f393,plain,
    ( ~ r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl6_83
  <=> ~ r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f1503,plain,
    ( r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_130 ),
    inference(subsumption_resolution,[],[f1500,f92])).

fof(f1500,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_130 ),
    inference(resolution,[],[f750,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f750,plain,
    ( r1_xboole_0(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl6_130 ),
    inference(avatar_component_clause,[],[f749])).

fof(f749,plain,
    ( spl6_130
  <=> r1_xboole_0(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_130])])).

fof(f1468,plain,
    ( ~ spl6_9
    | ~ spl6_2
    | ~ spl6_4
    | spl6_57 ),
    inference(avatar_split_clause,[],[f535,f484,f91,f87,f121])).

fof(f121,plain,
    ( spl6_9
  <=> ~ v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f484,plain,
    ( spl6_57
  <=> ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f535,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_57 ),
    inference(subsumption_resolution,[],[f105,f485])).

fof(f485,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f484])).

fof(f105,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f94,f88])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f92,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f1429,plain,
    ( spl6_300
    | ~ spl6_290 ),
    inference(avatar_split_clause,[],[f1410,f1405,f1427])).

fof(f1410,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK2)
    | ~ spl6_290 ),
    inference(resolution,[],[f1406,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t86_tops_1.p',symmetry_r1_xboole_0)).

fof(f1406,plain,
    ( r1_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl6_290 ),
    inference(avatar_component_clause,[],[f1405])).

fof(f751,plain,
    ( spl6_130
    | ~ spl6_84 ),
    inference(avatar_split_clause,[],[f463,f396,f749])).

fof(f396,plain,
    ( spl6_84
  <=> r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f463,plain,
    ( r1_xboole_0(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl6_84 ),
    inference(resolution,[],[f397,f80])).

fof(f397,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f396])).

fof(f489,plain,
    ( ~ spl6_57
    | spl6_102
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f166,f132,f87,f83,f487,f484])).

fof(f83,plain,
    ( spl6_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f132,plain,
    ( spl6_12
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f165,f84])).

fof(f84,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f83])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f153,f88])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl6_12 ),
    inference(resolution,[],[f133,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ v3_pre_topc(X2,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t86_tops_1.p',t80_tops_1)).

fof(f133,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f132])).

fof(f398,plain,
    ( spl6_56
    | spl6_84
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f174,f132,f87,f83,f396,f268])).

fof(f174,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f173,f84])).

fof(f173,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f157,f88])).

fof(f157,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f133,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r1_xboole_0(X1,sK3(X0,X1))
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f394,plain,
    ( ~ spl6_83
    | spl6_9
    | spl6_59
    | ~ spl6_60
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f376,f324,f275,f271,f121,f392])).

fof(f271,plain,
    ( spl6_59
  <=> k1_xboole_0 != sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f275,plain,
    ( spl6_60
  <=> v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f376,plain,
    ( ~ r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ spl6_9
    | ~ spl6_59
    | ~ spl6_60
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f375,f272])).

fof(f272,plain,
    ( k1_xboole_0 != sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f271])).

fof(f375,plain,
    ( ~ r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | k1_xboole_0 = sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl6_9
    | ~ spl6_60
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f360,f276])).

fof(f276,plain,
    ( v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f275])).

fof(f360,plain,
    ( ~ r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | k1_xboole_0 = sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl6_9
    | ~ spl6_74 ),
    inference(resolution,[],[f325,f347])).

fof(f347,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1)
        | ~ v3_pre_topc(X2,sK0)
        | k1_xboole_0 = X2 )
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f54,f122])).

fof(f122,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f54,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t86_tops_1.p',t86_tops_1)).

fof(f346,plain,
    ( spl6_78
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f345,f336,f340])).

fof(f345,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f50,f337])).

fof(f337,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f336])).

fof(f50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f342,plain,
    ( spl6_78
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f284,f268,f91,f87,f340])).

fof(f284,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f50,f281])).

fof(f334,plain,
    ( ~ spl6_77
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f327,f268,f91,f87,f332])).

fof(f327,plain,
    ( k1_xboole_0 != sK2
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_56 ),
    inference(subsumption_resolution,[],[f53,f281])).

fof(f53,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f326,plain,
    ( spl6_56
    | spl6_74
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f168,f132,f87,f83,f324,f268])).

fof(f168,plain,
    ( m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f167,f84])).

fof(f167,plain,
    ( ~ v2_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f154,f88])).

fof(f154,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f133,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f292,plain,
    ( ~ spl6_9
    | spl6_62 ),
    inference(avatar_split_clause,[],[f52,f289,f121])).

fof(f52,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f277,plain,
    ( spl6_56
    | spl6_60
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f172,f132,f87,f83,f275,f268])).

fof(f172,plain,
    ( v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f171,f84])).

fof(f171,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f156,f88])).

fof(f156,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f133,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK3(X0,X1),X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f273,plain,
    ( spl6_56
    | ~ spl6_59
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f170,f132,f87,f83,f271,f268])).

fof(f170,plain,
    ( k1_xboole_0 != sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f169,f84])).

fof(f169,plain,
    ( ~ v2_pre_topc(sK0)
    | k1_xboole_0 != sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f155,f88])).

fof(f155,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k1_xboole_0 != sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f133,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k1_xboole_0 != sK3(X0,X1)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f134,plain,
    ( spl6_12
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f100,f91,f132])).

fof(f100,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4 ),
    inference(resolution,[],[f92,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t86_tops_1.p',dt_k3_subset_1)).

fof(f126,plain,
    ( ~ spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f51,f124,f121])).

fof(f51,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f93,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f55,f91])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f89,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f57,f87])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f56,f83])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
