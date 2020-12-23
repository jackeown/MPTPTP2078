%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 205 expanded)
%              Number of leaves         :   20 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  358 ( 688 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f262,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f58,f63,f68,f76,f87,f101,f106,f117,f154,f232,f237,f241,f261])).

fof(f261,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_13
    | spl6_15
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_13
    | spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f259,f226])).

fof(f226,plain,
    ( ~ v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl6_15
  <=> v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f259,plain,
    ( v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f246,f230])).

fof(f230,plain,
    ( m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl6_16
  <=> m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f246,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f245,f44])).

fof(f44,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl6_2
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f245,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ v2_tops_2(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_5
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f242,f62])).

fof(f62,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f242,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ v2_tops_2(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_13 ),
    inference(resolution,[],[f149,f51])).

fof(f51,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v4_pre_topc(X1,sK0)
        | ~ v2_tops_2(X0,sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f39,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(f39,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f149,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_13
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f241,plain,
    ( ~ spl6_1
    | spl6_7
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl6_1
    | spl6_7
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f239,f75])).

fof(f75,plain,
    ( ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_7
  <=> v2_tops_2(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f239,plain,
    ( v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f238,f81])).

fof(f81,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_8
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f238,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_15 ),
    inference(resolution,[],[f227,f53])).

fof(f53,plain,
    ( ! [X3] :
        ( ~ v4_pre_topc(sK3(sK0,X3),sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X3,sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f39,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f227,plain,
    ( v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f225])).

fof(f237,plain,
    ( ~ spl6_1
    | spl6_7
    | ~ spl6_8
    | spl6_16 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl6_1
    | spl6_7
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f235,f75])).

fof(f235,plain,
    ( v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f234,f39])).

fof(f234,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_8
    | spl6_16 ),
    inference(subsumption_resolution,[],[f233,f81])).

fof(f233,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | spl6_16 ),
    inference(resolution,[],[f231,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f231,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f229])).

fof(f232,plain,
    ( spl6_15
    | ~ spl6_16
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f159,f151,f55,f47,f37,f229,f225])).

fof(f47,plain,
    ( spl6_3
  <=> v2_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f55,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f151,plain,
    ( spl6_14
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f159,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f158,f49])).

fof(f49,plain,
    ( v2_tops_2(sK2,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f158,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ v2_tops_2(sK2,sK0)
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f155,f57])).

fof(f57,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f155,plain,
    ( ~ m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)
    | ~ v2_tops_2(sK2,sK0)
    | ~ spl6_1
    | ~ spl6_14 ),
    inference(resolution,[],[f153,f51])).

fof(f153,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f154,plain,
    ( spl6_13
    | spl6_14
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f122,f114,f151,f147])).

fof(f114,plain,
    ( spl6_12
  <=> sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f122,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)
    | ~ spl6_12 ),
    inference(resolution,[],[f116,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f116,plain,
    ( sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( spl6_12
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f109,f84,f114])).

fof(f84,plain,
    ( spl6_9
  <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f109,plain,
    ( sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl6_9 ),
    inference(resolution,[],[f86,f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f86,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f106,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_8
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f104,f62])).

fof(f104,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4
    | spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f103,f57])).

fof(f103,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f102,f82])).

fof(f82,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f102,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_10 ),
    inference(superposition,[],[f90,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f90,plain,
    ( m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_10
  <=> m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f101,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | spl6_10 ),
    inference(subsumption_resolution,[],[f99,f62])).

fof(f99,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4
    | spl6_10 ),
    inference(subsumption_resolution,[],[f97,f57])).

fof(f97,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_10 ),
    inference(resolution,[],[f91,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f91,plain,
    ( ~ m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f87,plain,
    ( ~ spl6_8
    | spl6_9
    | ~ spl6_1
    | spl6_7 ),
    inference(avatar_split_clause,[],[f78,f73,f37,f84,f80])).

fof(f78,plain,
    ( r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_1
    | spl6_7 ),
    inference(resolution,[],[f52,f75])).

fof(f52,plain,
    ( ! [X2] :
        ( v2_tops_2(X2,sK0)
        | r2_hidden(sK3(sK0,X2),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl6_1 ),
    inference(resolution,[],[f39,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f76,plain,
    ( ~ spl6_7
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f71,f65,f60,f55,f73])).

fof(f65,plain,
    ( spl6_6
  <=> v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f71,plain,
    ( ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl6_4
    | ~ spl6_5
    | spl6_6 ),
    inference(subsumption_resolution,[],[f70,f62])).

fof(f70,plain,
    ( ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4
    | spl6_6 ),
    inference(subsumption_resolution,[],[f69,f57])).

fof(f69,plain,
    ( ~ v2_tops_2(k2_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_6 ),
    inference(superposition,[],[f67,f26])).

fof(f67,plain,
    ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f68,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f18,f65])).

fof(f18,plain,(
    ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X2,X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v2_tops_2(X2,X0)
                    & v2_tops_2(X1,X0) )
                 => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & v2_tops_2(X1,X0) )
               => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tops_2)).

fof(f63,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f19,f60])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f15,f55])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f17,f47])).

fof(f17,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f20,f37])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:09:07 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.47  % (26351)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (26341)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (26342)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (26348)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (26347)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (26343)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (26338)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (26349)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (26352)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (26345)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (26341)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f40,f45,f50,f58,f63,f68,f76,f87,f101,f106,f117,f154,f232,f237,f241,f261])).
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    ~spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_13 | spl6_15 | ~spl6_16),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f260])).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    $false | (~spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_13 | spl6_15 | ~spl6_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f259,f226])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    ~v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | spl6_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f225])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    spl6_15 <=> v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | (~spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_13 | ~spl6_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f246,f230])).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f229])).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    spl6_16 <=> m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | (~spl6_1 | ~spl6_2 | ~spl6_5 | ~spl6_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f245,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    v2_tops_2(sK1,sK0) | ~spl6_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    spl6_2 <=> v2_tops_2(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | ~v2_tops_2(sK1,sK0) | (~spl6_1 | ~spl6_5 | ~spl6_13)),
% 0.22/0.51    inference(subsumption_resolution,[],[f242,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    spl6_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | ~v2_tops_2(sK1,sK0) | (~spl6_1 | ~spl6_13)),
% 0.22/0.51    inference(resolution,[],[f149,f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(X1,sK0) | ~v2_tops_2(X0,sK0)) ) | ~spl6_1),
% 0.22/0.51    inference(resolution,[],[f39,f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X2,X1) | v4_pre_topc(X2,X0) | ~v2_tops_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : (v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> ! [X2] : ((v4_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v4_pre_topc(X2,X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    l1_pre_topc(sK0) | ~spl6_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    spl6_1 <=> l1_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.51  fof(f149,plain,(
% 0.22/0.51    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | ~spl6_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f147])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    spl6_13 <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    ~spl6_1 | spl6_7 | ~spl6_8 | ~spl6_15),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f240])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    $false | (~spl6_1 | spl6_7 | ~spl6_8 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f239,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ~v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | spl6_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    spl6_7 <=> v2_tops_2(k2_xboole_0(sK1,sK2),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | (~spl6_1 | ~spl6_8 | ~spl6_15)),
% 0.22/0.51    inference(subsumption_resolution,[],[f238,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    spl6_8 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | (~spl6_1 | ~spl6_15)),
% 0.22/0.51    inference(resolution,[],[f227,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X3] : (~v4_pre_topc(sK3(sK0,X3),sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_2(X3,sK0)) ) | ~spl6_1),
% 0.22/0.51    inference(resolution,[],[f39,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(sK3(X0,X1),X0) | v2_tops_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | ~spl6_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f225])).
% 0.22/0.51  fof(f237,plain,(
% 0.22/0.51    ~spl6_1 | spl6_7 | ~spl6_8 | spl6_16),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f236])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    $false | (~spl6_1 | spl6_7 | ~spl6_8 | spl6_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f235,f75])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | (~spl6_1 | ~spl6_8 | spl6_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f234,f39])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | (~spl6_8 | spl6_16)),
% 0.22/0.51    inference(subsumption_resolution,[],[f233,f81])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | spl6_16),
% 0.22/0.51    inference(resolution,[],[f231,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_tops_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f229])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    spl6_15 | ~spl6_16 | ~spl6_1 | ~spl6_3 | ~spl6_4 | ~spl6_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f159,f151,f55,f47,f37,f229,f225])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    spl6_3 <=> v2_tops_2(sK2,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl6_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    spl6_14 <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | (~spl6_1 | ~spl6_3 | ~spl6_4 | ~spl6_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f158,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    v2_tops_2(sK2,sK0) | ~spl6_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f47])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | ~v2_tops_2(sK2,sK0) | (~spl6_1 | ~spl6_4 | ~spl6_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f155,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f55])).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0,k2_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v4_pre_topc(sK3(sK0,k2_xboole_0(sK1,sK2)),sK0) | ~v2_tops_2(sK2,sK0) | (~spl6_1 | ~spl6_14)),
% 0.22/0.51    inference(resolution,[],[f153,f51])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | ~spl6_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f151])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    spl6_13 | spl6_14 | ~spl6_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f122,f114,f151,f147])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl6_12 <=> sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2) | r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),sK1) | ~spl6_12),
% 0.22/0.51    inference(resolution,[],[f116,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1) | ~spl6_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f114])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl6_12 | ~spl6_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f109,f84,f114])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    spl6_9 <=> r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    sP5(sK3(sK0,k2_xboole_0(sK1,sK2)),sK2,sK1) | ~spl6_9),
% 0.22/0.51    inference(resolution,[],[f86,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | sP5(X3,X1,X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) | ~spl6_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f84])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    ~spl6_4 | ~spl6_5 | spl6_8 | ~spl6_10),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f105])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    $false | (~spl6_4 | ~spl6_5 | spl6_8 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f104,f62])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_4 | spl6_8 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f103,f57])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (spl6_8 | ~spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f102,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl6_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f80])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_10),
% 0.22/0.51    inference(superposition,[],[f90,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl6_10 <=> m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ~spl6_4 | ~spl6_5 | spl6_10),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f100])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    $false | (~spl6_4 | ~spl6_5 | spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f99,f62])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_4 | spl6_10)),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f57])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl6_10),
% 0.22/0.51    inference(resolution,[],[f91,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    ~m1_subset_1(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl6_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f89])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ~spl6_8 | spl6_9 | ~spl6_1 | spl6_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f78,f73,f37,f84,f80])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    r2_hidden(sK3(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_1 | spl6_7)),
% 0.22/0.51    inference(resolution,[],[f52,f75])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X2] : (v2_tops_2(X2,sK0) | r2_hidden(sK3(sK0,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl6_1),
% 0.22/0.51    inference(resolution,[],[f39,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1),X1) | v2_tops_2(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ~spl6_7 | ~spl6_4 | ~spl6_5 | spl6_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f71,f65,f60,f55,f73])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl6_6 <=> v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ~v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | (~spl6_4 | ~spl6_5 | spl6_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f70,f62])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ~v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_4 | spl6_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f69,f57])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ~v2_tops_2(k2_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl6_6),
% 0.22/0.51    inference(superposition,[],[f67,f26])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) | spl6_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f65])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ~spl6_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f18,f65])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & v2_tops_2(X2,X0) & v2_tops_2(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) & (v2_tops_2(X2,X0) & v2_tops_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & v2_tops_2(X1,X0)) => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.22/0.51    inference(negated_conjecture,[],[f5])).
% 0.22/0.51  fof(f5,conjecture,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ((v2_tops_2(X2,X0) & v2_tops_2(X1,X0)) => v2_tops_2(k4_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tops_2)).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    spl6_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f60])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    spl6_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f15,f55])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    spl6_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f17,f47])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    v2_tops_2(sK2,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    spl6_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f16,f42])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    v2_tops_2(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    spl6_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f37])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (26341)------------------------------
% 0.22/0.51  % (26341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26341)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (26341)Memory used [KB]: 10746
% 0.22/0.51  % (26341)Time elapsed: 0.094 s
% 0.22/0.51  % (26341)------------------------------
% 0.22/0.51  % (26341)------------------------------
% 0.22/0.51  % (26337)Success in time 0.143 s
%------------------------------------------------------------------------------
