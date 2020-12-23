%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 189 expanded)
%              Number of leaves         :   30 (  80 expanded)
%              Depth                    :    7
%              Number of atoms          :  287 ( 475 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f321,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f81,f86,f91,f96,f111,f128,f139,f142,f175,f226,f231,f237,f240,f271,f303,f315,f320])).

fof(f320,plain,
    ( ~ spl4_7
    | spl4_30 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl4_7
    | spl4_30 ),
    inference(unit_resulting_resolution,[],[f85,f314,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f314,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl4_30
  <=> r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f85,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_7
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f315,plain,
    ( ~ spl4_30
    | spl4_29 ),
    inference(avatar_split_clause,[],[f305,f300,f312])).

fof(f300,plain,
    ( spl4_29
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f305,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))
    | spl4_29 ),
    inference(resolution,[],[f302,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f302,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f300])).

fof(f303,plain,
    ( ~ spl4_29
    | spl4_17
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f280,f268,f172,f300])).

fof(f172,plain,
    ( spl4_17
  <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f268,plain,
    ( spl4_25
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f280,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | spl4_17
    | ~ spl4_25 ),
    inference(resolution,[],[f244,f270])).

fof(f270,plain,
    ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f268])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),X0)
        | ~ r1_xboole_0(X0,k1_tops_1(sK0,sK2)) )
    | spl4_17 ),
    inference(resolution,[],[f174,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

% (15413)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f174,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f172])).

fof(f271,plain,
    ( spl4_25
    | ~ spl4_2
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f241,f223,f54,f268])).

% (15430)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (15422)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f54,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f223,plain,
    ( spl4_21
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f241,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))
    | ~ spl4_21 ),
    inference(resolution,[],[f224,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f224,plain,
    ( m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f240,plain,
    ( ~ spl4_6
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl4_6
    | spl4_22 ),
    inference(unit_resulting_resolution,[],[f80,f36,f236,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f236,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl4_22
  <=> r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f80,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f237,plain,
    ( ~ spl4_22
    | spl4_21 ),
    inference(avatar_split_clause,[],[f232,f223,f234])).

fof(f232,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl4_21 ),
    inference(resolution,[],[f225,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f225,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f223])).

fof(f231,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl4_20 ),
    inference(unit_resulting_resolution,[],[f36,f221])).

fof(f221,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl4_20
  <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f226,plain,
    ( ~ spl4_2
    | ~ spl4_20
    | ~ spl4_4
    | ~ spl4_21
    | spl4_16 ),
    inference(avatar_split_clause,[],[f185,f168,f223,f64,f219,f54])).

fof(f64,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f168,plain,
    ( spl4_16
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f185,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | spl4_16 ),
    inference(resolution,[],[f170,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f170,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f168])).

fof(f175,plain,
    ( ~ spl4_16
    | ~ spl4_17
    | spl4_12 ),
    inference(avatar_split_clause,[],[f153,f125,f172,f168])).

fof(f125,plain,
    ( spl4_12
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f153,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl4_12 ),
    inference(resolution,[],[f127,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f127,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f142,plain,
    ( ~ spl4_6
    | ~ spl4_8
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_8
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f80,f90,f138,f47])).

fof(f138,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl4_14
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f90,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_8
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f139,plain,
    ( ~ spl4_14
    | spl4_11 ),
    inference(avatar_split_clause,[],[f134,f121,f136])).

fof(f121,plain,
    ( spl4_11
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f134,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl4_11 ),
    inference(resolution,[],[f123,f41])).

fof(f123,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f128,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | spl4_10 ),
    inference(avatar_split_clause,[],[f113,f108,f125,f121])).

fof(f108,plain,
    ( spl4_10
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f113,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_10 ),
    inference(superposition,[],[f110,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f110,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f111,plain,
    ( ~ spl4_4
    | ~ spl4_10
    | spl4_9 ),
    inference(avatar_split_clause,[],[f98,f93,f108,f64])).

fof(f93,plain,
    ( spl4_9
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f98,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_9 ),
    inference(superposition,[],[f95,f44])).

fof(f95,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f96,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f30,f93])).

fof(f30,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(f91,plain,
    ( spl4_8
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f75,f64,f54,f88])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f66,f34])).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f86,plain,
    ( spl4_7
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f68,f59,f54,f83])).

fof(f59,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f68,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f61,f34])).

fof(f61,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f81,plain,
    ( spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f76,f64,f78])).

fof(f76,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f66,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f67,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f29,f59])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f33,f54])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n004.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:16:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (15435)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (15427)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (15419)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (15415)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (15414)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (15421)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (15431)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (15417)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (15418)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (15436)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (15435)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f321,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f57,f62,f67,f81,f86,f91,f96,f111,f128,f139,f142,f175,f226,f231,f237,f240,f271,f303,f315,f320])).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    ~spl4_7 | spl4_30),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f316])).
% 0.21/0.54  fof(f316,plain,(
% 0.21/0.54    $false | (~spl4_7 | spl4_30)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f85,f314,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.21/0.54  fof(f314,plain,(
% 0.21/0.54    ~r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) | spl4_30),
% 0.21/0.54    inference(avatar_component_clause,[],[f312])).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    spl4_30 <=> r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    spl4_7 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f315,plain,(
% 0.21/0.54    ~spl4_30 | spl4_29),
% 0.21/0.54    inference(avatar_split_clause,[],[f305,f300,f312])).
% 0.21/0.54  fof(f300,plain,(
% 0.21/0.54    spl4_29 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    ~r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) | spl4_29),
% 0.21/0.54    inference(resolution,[],[f302,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | spl4_29),
% 0.21/0.54    inference(avatar_component_clause,[],[f300])).
% 0.21/0.54  fof(f303,plain,(
% 0.21/0.54    ~spl4_29 | spl4_17 | ~spl4_25),
% 0.21/0.54    inference(avatar_split_clause,[],[f280,f268,f172,f300])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    spl4_17 <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    spl4_25 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.54  fof(f280,plain,(
% 0.21/0.54    ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | (spl4_17 | ~spl4_25)),
% 0.21/0.54    inference(resolution,[],[f244,f270])).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) | ~spl4_25),
% 0.21/0.54    inference(avatar_component_clause,[],[f268])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),X0) | ~r1_xboole_0(X0,k1_tops_1(sK0,sK2))) ) | spl4_17),
% 0.21/0.54    inference(resolution,[],[f174,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.54  % (15413)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | spl4_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f172])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    spl4_25 | ~spl4_2 | ~spl4_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f241,f223,f54,f268])).
% 0.21/0.54  % (15430)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (15422)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    spl4_2 <=> l1_pre_topc(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    spl4_21 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(sK1,sK2)) | ~spl4_21),
% 0.21/0.54    inference(resolution,[],[f224,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f223])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    ~spl4_6 | spl4_22),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f238])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    $false | (~spl4_6 | spl4_22)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f80,f36,f236,f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl4_22),
% 0.21/0.54    inference(avatar_component_clause,[],[f234])).
% 0.21/0.54  fof(f234,plain,(
% 0.21/0.54    spl4_22 <=> r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    spl4_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    ~spl4_22 | spl4_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f232,f223,f234])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl4_21),
% 0.21/0.54    inference(resolution,[],[f225,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f223])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    spl4_20),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f227])).
% 0.21/0.54  fof(f227,plain,(
% 0.21/0.54    $false | spl4_20),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f36,f221])).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | spl4_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f219])).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    spl4_20 <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    ~spl4_2 | ~spl4_20 | ~spl4_4 | ~spl4_21 | spl4_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f185,f168,f223,f64,f219,f54])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    spl4_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    spl4_16 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0) | spl4_16),
% 0.21/0.54    inference(resolution,[],[f170,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | spl4_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f168])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ~spl4_16 | ~spl4_17 | spl4_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f153,f125,f172,f168])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    spl4_12 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | spl4_12),
% 0.21/0.54    inference(resolution,[],[f127,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl4_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f125])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    ~spl4_6 | ~spl4_8 | spl4_14),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    $false | (~spl4_6 | ~spl4_8 | spl4_14)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f80,f90,f138,f47])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl4_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f136])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl4_14 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f88])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    spl4_8 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.54  fof(f139,plain,(
% 0.21/0.54    ~spl4_14 | spl4_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f134,f121,f136])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    spl4_11 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl4_11),
% 0.21/0.54    inference(resolution,[],[f123,f41])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f121])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    ~spl4_11 | ~spl4_12 | spl4_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f113,f108,f125,f121])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    spl4_10 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_10),
% 0.21/0.54    inference(superposition,[],[f110,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl4_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f108])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ~spl4_4 | ~spl4_10 | spl4_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f98,f93,f108,f64])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    spl4_9 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_9),
% 0.21/0.54    inference(superposition,[],[f95,f44])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl4_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f93])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    ~spl4_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f30,f93])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    spl4_8 | ~spl4_2 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f75,f64,f54,f88])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_4),
% 0.21/0.54    inference(resolution,[],[f66,f34])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f64])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    spl4_7 | ~spl4_2 | ~spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f68,f59,f54,f83])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    spl4_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f61,f34])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f59])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    spl4_6 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f76,f64,f78])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.54    inference(resolution,[],[f66,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f31,f64])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f29,f59])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f33,f54])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    l1_pre_topc(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (15435)------------------------------
% 0.21/0.54  % (15435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15435)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (15435)Memory used [KB]: 11001
% 0.21/0.54  % (15435)Time elapsed: 0.071 s
% 0.21/0.54  % (15435)------------------------------
% 0.21/0.54  % (15435)------------------------------
% 0.21/0.54  % (15439)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (15437)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (15416)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (15441)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (15442)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (15412)Success in time 0.185 s
%------------------------------------------------------------------------------
