%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 364 expanded)
%              Number of leaves         :   40 ( 146 expanded)
%              Depth                    :   11
%              Number of atoms          :  638 (1080 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f443,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f90,f101,f117,f124,f129,f135,f149,f156,f160,f174,f181,f189,f193,f197,f211,f215,f243,f336,f362,f408,f432,f441,f442])).

fof(f442,plain,
    ( u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f441,plain,
    ( spl4_8
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | spl4_8
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f439,f128])).

fof(f128,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl4_8
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f439,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_16
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f437,f188])).

fof(f188,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl4_16
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f437,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_39 ),
    inference(resolution,[],[f431,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f431,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl4_39
  <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f432,plain,
    ( spl4_39
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_12
    | spl4_15
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f381,f213,f179,f158,f119,f99,f88,f430])).

fof(f88,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f99,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f119,plain,
    ( spl4_6
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f158,plain,
    ( spl4_12
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f179,plain,
    ( spl4_15
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f213,plain,
    ( spl4_20
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f381,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_12
    | spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f377,f380])).

fof(f380,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f245,f120])).

fof(f120,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f245,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f244,f89])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f244,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_12
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f216,f159])).

fof(f159,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f158])).

fof(f216,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_20 ),
    inference(resolution,[],[f214,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f214,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f213])).

fof(f377,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_4
    | ~ spl4_6
    | spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f374,f376])).

fof(f376,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f113,f375])).

fof(f375,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f53,f120])).

fof(f53,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

fof(f113,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f106,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f106,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f100,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f100,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f374,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | spl4_15
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f220,f210])).

% (19597)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f210,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f179])).

fof(f220,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_20 ),
    inference(resolution,[],[f214,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0)
      | ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_subset_1(X1,X0)
           => v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).

fof(f408,plain,
    ( spl4_27
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f402,f208,f154,f278])).

fof(f278,plain,
    ( spl4_27
  <=> v2_struct_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f154,plain,
    ( spl4_11
  <=> l1_struct_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f208,plain,
    ( spl4_19
  <=> v1_xboole_0(u1_struct_0(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f402,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ spl4_11
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f400,f155])).

fof(f155,plain,
    ( l1_struct_0(sK3(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f400,plain,
    ( ~ l1_struct_0(sK3(sK0))
    | v2_struct_0(sK3(sK0))
    | ~ spl4_19 ),
    inference(resolution,[],[f209,f75])).

fof(f209,plain,
    ( v1_xboole_0(u1_struct_0(sK3(sK0)))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f208])).

fof(f362,plain,
    ( spl4_37
    | ~ spl4_2
    | spl4_6
    | ~ spl4_12
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f286,f241,f213,f158,f119,f88,f360])).

fof(f360,plain,
    ( spl4_37
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f241,plain,
    ( spl4_23
  <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f286,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | spl4_6
    | ~ spl4_12
    | ~ spl4_20
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f217,f285])).

fof(f285,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_2
    | spl4_6
    | ~ spl4_12
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f284,f130])).

fof(f130,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f284,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f283,f89])).

fof(f283,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_12
    | ~ spl4_23 ),
    inference(subsumption_resolution,[],[f282,f159])).

fof(f282,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_23 ),
    inference(superposition,[],[f65,f242])).

fof(f242,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f241])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f217,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl4_20 ),
    inference(resolution,[],[f214,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f336,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f334,f85])).

fof(f85,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f334,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_2
    | ~ spl4_27 ),
    inference(subsumption_resolution,[],[f333,f89])).

fof(f333,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_27 ),
    inference(resolution,[],[f279,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_struct_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v1_pre_topc(X1)
          & ~ v2_struct_0(X1)
          & m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_pre_topc)).

fof(f279,plain,
    ( v2_struct_0(sK3(sK0))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f278])).

fof(f243,plain,
    ( spl4_23
    | ~ spl4_2
    | spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f170,f158,f119,f88,f241])).

fof(f170,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f169,f130])).

fof(f169,plain,
    ( u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f164,f89])).

fof(f164,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_12 ),
    inference(resolution,[],[f159,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f215,plain,
    ( spl4_20
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f166,f158,f88,f213])).

fof(f166,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f162,f89])).

fof(f162,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_12 ),
    inference(resolution,[],[f159,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f211,plain,
    ( spl4_19
    | ~ spl4_15
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f200,f195,f179,f208])).

fof(f195,plain,
    ( spl4_18
  <=> m1_subset_1(u1_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f200,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK3(sK0)))
    | ~ spl4_18 ),
    inference(resolution,[],[f196,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f196,plain,
    ( m1_subset_1(u1_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f141,f115,f88,f195])).

fof(f115,plain,
    ( spl4_5
  <=> m1_pre_topc(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f141,plain,
    ( m1_subset_1(u1_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f137,f89])).

fof(f137,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(resolution,[],[f116,f71])).

fof(f116,plain,
    ( m1_pre_topc(sK3(sK0),sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f193,plain,
    ( spl4_17
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f184,f172,f133,f191])).

fof(f191,plain,
    ( spl4_17
  <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f133,plain,
    ( spl4_9
  <=> v7_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f172,plain,
    ( spl4_13
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f184,plain,
    ( v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f152,f182])).

fof(f182,plain,
    ( l1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_13 ),
    inference(resolution,[],[f173,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f173,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f172])).

fof(f152,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))
    | ~ spl4_9 ),
    inference(resolution,[],[f134,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f134,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f189,plain,
    ( spl4_16
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f182,f172,f187])).

fof(f181,plain,
    ( ~ spl4_14
    | spl4_15
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f145,f122,f99,f179,f176])).

fof(f176,plain,
    ( spl4_14
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f122,plain,
    ( spl4_7
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f145,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f144,f100])).

fof(f144,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f123,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f123,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f174,plain,
    ( spl4_13
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f165,f158,f88,f172])).

fof(f165,plain,
    ( l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f161,f89])).

fof(f161,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl4_12 ),
    inference(resolution,[],[f159,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

fof(f160,plain,
    ( spl4_12
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f112,f99,f88,f84,f158])).

fof(f112,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f111,f85])).

fof(f111,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f105,f89])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f100,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f156,plain,
    ( spl4_11
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f150,f147,f154])).

fof(f147,plain,
    ( spl4_10
  <=> l1_pre_topc(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f150,plain,
    ( l1_struct_0(sK3(sK0))
    | ~ spl4_10 ),
    inference(resolution,[],[f148,f80])).

fof(f148,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( spl4_10
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f140,f115,f88,f147])).

fof(f140,plain,
    ( l1_pre_topc(sK3(sK0))
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f136,f89])).

fof(f136,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3(sK0))
    | ~ spl4_5 ),
    inference(resolution,[],[f116,f72])).

fof(f135,plain,
    ( spl4_9
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f110,f99,f88,f84,f133])).

fof(f110,plain,
    ( v7_struct_0(k1_tex_2(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f109,f85])).

fof(f109,plain,
    ( v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f103,f89])).

fof(f103,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v7_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f100,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f129,plain,
    ( ~ spl4_8
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f108,f99,f88,f84,f127])).

fof(f108,plain,
    ( ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f107,f85])).

fof(f107,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f102,f89])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl4_4 ),
    inference(resolution,[],[f100,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,
    ( spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f52,f122,f119])).

fof(f52,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f117,plain,
    ( spl4_5
    | spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f93,f88,f84,f115])).

fof(f93,plain,
    ( m1_pre_topc(sK3(sK0),sK0)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f92,f85])).

fof(f92,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(sK3(sK0),sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f89,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_pre_topc(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f54,f99])).

fof(f54,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f56,f88])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f55,f84])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:13:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (19595)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (19594)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (19593)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (19607)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (19593)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f443,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f86,f90,f101,f117,f124,f129,f135,f149,f156,f160,f174,f181,f189,f193,f197,f211,f215,f243,f336,f362,f408,f432,f441,f442])).
% 0.21/0.49  fof(f442,plain,(
% 0.21/0.49    u1_struct_0(sK0) != u1_struct_0(k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f441,plain,(
% 0.21/0.49    spl4_8 | ~spl4_16 | ~spl4_39),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f440])).
% 0.21/0.49  fof(f440,plain,(
% 0.21/0.49    $false | (spl4_8 | ~spl4_16 | ~spl4_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f439,f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~v2_struct_0(k1_tex_2(sK0,sK1)) | spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl4_8 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f439,plain,(
% 0.21/0.49    v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_16 | ~spl4_39)),
% 0.21/0.49    inference(subsumption_resolution,[],[f437,f188])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f187])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    spl4_16 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f437,plain,(
% 0.21/0.49    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_39),
% 0.21/0.49    inference(resolution,[],[f431,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.49  fof(f431,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl4_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f430])).
% 0.21/0.49  fof(f430,plain,(
% 0.21/0.49    spl4_39 <=> v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.49  fof(f432,plain,(
% 0.21/0.49    spl4_39 | ~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_12 | spl4_15 | ~spl4_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f381,f213,f179,f158,f119,f99,f88,f430])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    spl4_2 <=> l1_pre_topc(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl4_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl4_6 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    spl4_12 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl4_15 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    spl4_20 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.49  fof(f381,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | (~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_12 | spl4_15 | ~spl4_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f377,f380])).
% 0.21/0.49  fof(f380,plain,(
% 0.21/0.49    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl4_2 | ~spl4_6 | ~spl4_12 | ~spl4_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f245,f120])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f119])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_12 | ~spl4_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f244,f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    l1_pre_topc(sK0) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f88])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_12 | ~spl4_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f216,f159])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl4_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f158])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_20),
% 0.21/0.49    inference(resolution,[],[f214,f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f213])).
% 0.21/0.49  fof(f377,plain,(
% 0.21/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | (~spl4_4 | ~spl4_6 | spl4_15 | ~spl4_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f374,f376])).
% 0.21/0.49  fof(f376,plain,(
% 0.21/0.49    v1_zfmisc_1(u1_struct_0(sK0)) | (~spl4_4 | ~spl4_6)),
% 0.21/0.49    inference(subsumption_resolution,[],[f113,f375])).
% 0.21/0.49  fof(f375,plain,(
% 0.21/0.49    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f53,f120])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f18])).
% 0.21/0.49  fof(f18,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    v1_zfmisc_1(u1_struct_0(sK0)) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f106,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f100,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0) | v1_subset_1(k6_domain_1(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,axiom,(
% 0.21/0.49    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f99])).
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    ~v1_zfmisc_1(u1_struct_0(sK0)) | ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | (spl4_15 | ~spl4_20)),
% 0.21/0.49    inference(subsumption_resolution,[],[f220,f210])).
% 0.21/0.49  % (19597)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f179])).
% 0.21/0.49  fof(f220,plain,(
% 0.21/0.49    ~v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl4_20),
% 0.21/0.49    inference(resolution,[],[f214,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | ~v1_subset_1(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) => v1_xboole_0(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).
% 0.21/0.49  fof(f408,plain,(
% 0.21/0.49    spl4_27 | ~spl4_11 | ~spl4_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f402,f208,f154,f278])).
% 0.21/0.49  fof(f278,plain,(
% 0.21/0.49    spl4_27 <=> v2_struct_0(sK3(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl4_11 <=> l1_struct_0(sK3(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    spl4_19 <=> v1_xboole_0(u1_struct_0(sK3(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.49  fof(f402,plain,(
% 0.21/0.49    v2_struct_0(sK3(sK0)) | (~spl4_11 | ~spl4_19)),
% 0.21/0.49    inference(subsumption_resolution,[],[f400,f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    l1_struct_0(sK3(sK0)) | ~spl4_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f154])).
% 0.21/0.49  fof(f400,plain,(
% 0.21/0.49    ~l1_struct_0(sK3(sK0)) | v2_struct_0(sK3(sK0)) | ~spl4_19),
% 0.21/0.49    inference(resolution,[],[f209,f75])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK3(sK0))) | ~spl4_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f208])).
% 0.21/0.49  fof(f362,plain,(
% 0.21/0.49    spl4_37 | ~spl4_2 | spl4_6 | ~spl4_12 | ~spl4_20 | ~spl4_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f286,f241,f213,f158,f119,f88,f360])).
% 0.21/0.49  fof(f360,plain,(
% 0.21/0.49    spl4_37 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    spl4_23 <=> u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_2 | spl4_6 | ~spl4_12 | ~spl4_20 | ~spl4_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f217,f285])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl4_2 | spl4_6 | ~spl4_12 | ~spl4_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f284,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f119])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_12 | ~spl4_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f283,f89])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_12 | ~spl4_23)),
% 0.21/0.49    inference(subsumption_resolution,[],[f282,f159])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_23),
% 0.21/0.49    inference(superposition,[],[f65,f242])).
% 0.21/0.49  fof(f242,plain,(
% 0.21/0.49    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | ~spl4_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f241])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f217,plain,(
% 0.21/0.49    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl4_20),
% 0.21/0.49    inference(resolution,[],[f214,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    spl4_1 | ~spl4_2 | ~spl4_27),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f335])).
% 0.21/0.49  fof(f335,plain,(
% 0.21/0.49    $false | (spl4_1 | ~spl4_2 | ~spl4_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f334,f85])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f334,plain,(
% 0.21/0.49    v2_struct_0(sK0) | (~spl4_2 | ~spl4_27)),
% 0.21/0.49    inference(subsumption_resolution,[],[f333,f89])).
% 0.21/0.49  fof(f333,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_27),
% 0.21/0.49    inference(resolution,[],[f279,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_struct_0(sK3(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0] : (? [X1] : (~v2_struct_0(X1) & m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v2_struct_0(X1) & m1_pre_topc(X1,X0)))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v1_pre_topc(X1) & ~v2_struct_0(X1) & m1_pre_topc(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc4_pre_topc)).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    v2_struct_0(sK3(sK0)) | ~spl4_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f278])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    spl4_23 | ~spl4_2 | spl4_6 | ~spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f170,f158,f119,f88,f241])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | (~spl4_2 | spl4_6 | ~spl4_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f169,f130])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f164,f89])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | u1_struct_0(k1_tex_2(sK0,sK1)) = sK2(sK0,k1_tex_2(sK0,sK1)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl4_12),
% 0.21/0.49    inference(resolution,[],[f159,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tex_2(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    spl4_20 | ~spl4_2 | ~spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f166,f158,f88,f213])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f162,f89])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_12),
% 0.21/0.49    inference(resolution,[],[f159,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    spl4_19 | ~spl4_15 | ~spl4_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f200,f195,f179,f208])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    spl4_18 <=> m1_subset_1(u1_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK3(sK0))) | ~spl4_18),
% 0.21/0.49    inference(resolution,[],[f196,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    m1_subset_1(u1_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f195])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    spl4_18 | ~spl4_2 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f141,f115,f88,f195])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl4_5 <=> m1_pre_topc(sK3(sK0),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    m1_subset_1(u1_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f137,f89])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f116,f71])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    m1_pre_topc(sK3(sK0),sK0) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f115])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    spl4_17 | ~spl4_9 | ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f184,f172,f133,f191])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl4_17 <=> v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    spl4_9 <=> v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    spl4_13 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | (~spl4_9 | ~spl4_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f152,f182])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    l1_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_13),
% 0.21/0.49    inference(resolution,[],[f173,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f172])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK0,sK1))) | ~spl4_9),
% 0.21/0.49    inference(resolution,[],[f134,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f133])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    spl4_16 | ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f182,f172,f187])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ~spl4_14 | spl4_15 | ~spl4_4 | ~spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f145,f122,f99,f179,f176])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    spl4_14 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl4_7 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    v1_xboole_0(u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0)) | (~spl4_4 | ~spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f144,f100])).
% 0.21/0.49  fof(f144,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_zfmisc_1(u1_struct_0(sK0)) | ~spl4_7),
% 0.21/0.49    inference(resolution,[],[f123,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    spl4_13 | ~spl4_2 | ~spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f165,f158,f88,f172])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    l1_pre_topc(k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_12)),
% 0.21/0.49    inference(subsumption_resolution,[],[f161,f89])).
% 0.21/0.49  fof(f161,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | l1_pre_topc(k1_tex_2(sK0,sK1)) | ~spl4_12),
% 0.21/0.49    inference(resolution,[],[f159,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    spl4_12 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f112,f99,f88,f84,f158])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f111,f85])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f105,f89])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f100,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    spl4_11 | ~spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f150,f147,f154])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    spl4_10 <=> l1_pre_topc(sK3(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    l1_struct_0(sK3(sK0)) | ~spl4_10),
% 0.21/0.49    inference(resolution,[],[f148,f80])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    l1_pre_topc(sK3(sK0)) | ~spl4_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f147])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    spl4_10 | ~spl4_2 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f140,f115,f88,f147])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    l1_pre_topc(sK3(sK0)) | (~spl4_2 | ~spl4_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f136,f89])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | l1_pre_topc(sK3(sK0)) | ~spl4_5),
% 0.21/0.49    inference(resolution,[],[f116,f72])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl4_9 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f110,f99,f88,f84,f133])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    v7_struct_0(k1_tex_2(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f85])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f103,f89])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v7_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f100,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v7_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.49  fof(f14,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~spl4_8 | spl4_1 | ~spl4_2 | ~spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f108,f99,f88,f84,f127])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ~v2_struct_0(k1_tex_2(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f107,f85])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl4_2 | ~spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f102,f89])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f100,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    spl4_6 | spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f122,f119])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl4_5 | spl4_1 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f93,f88,f84,f115])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    m1_pre_topc(sK3(sK0),sK0) | (spl4_1 | ~spl4_2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f92,f85])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    v2_struct_0(sK0) | m1_pre_topc(sK3(sK0),sK0) | ~spl4_2),
% 0.21/0.49    inference(resolution,[],[f89,f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(sK3(X0),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f44])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f54,f99])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f56,f88])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ~spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f84])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (19593)------------------------------
% 0.21/0.49  % (19593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19593)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (19593)Memory used [KB]: 6396
% 0.21/0.49  % (19593)Time elapsed: 0.066 s
% 0.21/0.49  % (19593)------------------------------
% 0.21/0.49  % (19593)------------------------------
% 0.21/0.49  % (19598)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (19608)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (19592)Success in time 0.135 s
%------------------------------------------------------------------------------
