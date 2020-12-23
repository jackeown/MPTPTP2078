%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1307+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:42 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 154 expanded)
%              Number of leaves         :   17 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  261 ( 467 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f55,f60,f67,f78,f91,f95,f105,f116,f159,f164,f168])).

fof(f168,plain,
    ( ~ spl6_1
    | spl6_6
    | ~ spl6_7
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl6_1
    | spl6_6
    | ~ spl6_7
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f166,f66])).

fof(f66,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_6
  <=> v2_tops_2(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f166,plain,
    ( v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_7
    | ~ spl6_13 ),
    inference(subsumption_resolution,[],[f165,f72])).

fof(f72,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_7
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f165,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_13 ),
    inference(resolution,[],[f154,f45])).

fof(f45,plain,
    ( ! [X3] :
        ( ~ v4_pre_topc(sK3(sK0,X3),sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X3,sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f36,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_2)).

fof(f36,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f154,plain,
    ( v4_pre_topc(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl6_13
  <=> v4_pre_topc(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f164,plain,
    ( ~ spl6_1
    | spl6_6
    | ~ spl6_7
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl6_1
    | spl6_6
    | ~ spl6_7
    | spl6_14 ),
    inference(subsumption_resolution,[],[f162,f66])).

fof(f162,plain,
    ( v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl6_1
    | ~ spl6_7
    | spl6_14 ),
    inference(subsumption_resolution,[],[f161,f36])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl6_7
    | spl6_14 ),
    inference(subsumption_resolution,[],[f160,f72])).

fof(f160,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | spl6_14 ),
    inference(resolution,[],[f158,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f158,plain,
    ( ~ m1_subset_1(sK3(sK0,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl6_14
  <=> m1_subset_1(sK3(sK0,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f159,plain,
    ( spl6_13
    | ~ spl6_14
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f122,f113,f52,f39,f34,f156,f152])).

fof(f39,plain,
    ( spl6_2
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f52,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f113,plain,
    ( spl6_12
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f122,plain,
    ( ~ m1_subset_1(sK3(sK0,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f121,f41])).

fof(f41,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f121,plain,
    ( ~ m1_subset_1(sK3(sK0,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ v2_tops_2(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f118,f54])).

fof(f54,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f118,plain,
    ( ~ m1_subset_1(sK3(sK0,k4_xboole_0(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(sK3(sK0,k4_xboole_0(sK1,sK2)),sK0)
    | ~ v2_tops_2(sK1,sK0)
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(resolution,[],[f115,f43])).

fof(f43,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v4_pre_topc(X1,sK0)
        | ~ v2_tops_2(X0,sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f36,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f115,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f113])).

fof(f116,plain,
    ( spl6_12
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f110,f102,f113])).

fof(f102,plain,
    ( spl6_11
  <=> sP5(sK3(sK0,k4_xboole_0(sK1,sK2)),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f110,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),sK1)
    | ~ spl6_11 ),
    inference(resolution,[],[f104,f25])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f104,plain,
    ( sP5(sK3(sK0,k4_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f105,plain,
    ( spl6_11
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f97,f75,f102])).

fof(f75,plain,
    ( spl6_8
  <=> r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f97,plain,
    ( sP5(sK3(sK0,k4_xboole_0(sK1,sK2)),sK2,sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f77,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f77,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f95,plain,
    ( ~ spl6_4
    | spl6_7
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl6_4
    | spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f93,f54])).

fof(f93,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f92,f73])).

fof(f73,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f92,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_9 ),
    inference(superposition,[],[f81,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f81,plain,
    ( m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_9
  <=> m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f91,plain,
    ( ~ spl6_4
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl6_4
    | spl6_9 ),
    inference(subsumption_resolution,[],[f88,f54])).

fof(f88,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_9 ),
    inference(resolution,[],[f82,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f82,plain,
    ( ~ m1_subset_1(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f78,plain,
    ( ~ spl6_7
    | spl6_8
    | ~ spl6_1
    | spl6_6 ),
    inference(avatar_split_clause,[],[f69,f64,f34,f75,f71])).

fof(f69,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_1
    | spl6_6 ),
    inference(resolution,[],[f44,f66])).

fof(f44,plain,
    ( ! [X2] :
        ( v2_tops_2(X2,sK0)
        | r2_hidden(sK3(sK0,X2),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl6_1 ),
    inference(resolution,[],[f36,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,
    ( ~ spl6_6
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f62,f57,f52,f64])).

fof(f57,plain,
    ( spl6_5
  <=> v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f62,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl6_4
    | spl6_5 ),
    inference(subsumption_resolution,[],[f61,f54])).

fof(f61,plain,
    ( ~ v2_tops_2(k4_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_5 ),
    inference(superposition,[],[f59,f23])).

fof(f59,plain,
    ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f60,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f15,f57])).

fof(f15,plain,(
    ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(sK0)),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
              & v2_tops_2(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0)
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
               => ( v2_tops_2(X1,X0)
                 => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( v2_tops_2(X1,X0)
               => v2_tops_2(k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tops_2)).

fof(f55,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f16,f52])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f14,f39])).

fof(f14,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f17,f34])).

fof(f17,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
