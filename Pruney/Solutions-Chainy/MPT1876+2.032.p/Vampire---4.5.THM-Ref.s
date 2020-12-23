%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:40 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 529 expanded)
%              Number of leaves         :   43 ( 214 expanded)
%              Depth                    :   21
%              Number of atoms          :  821 (2260 expanded)
%              Number of equality atoms :   26 (  87 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f887,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f111,f116,f121,f126,f131,f140,f179,f193,f270,f296,f346,f445,f469,f598,f603,f610,f636,f774,f800,f812,f862,f877,f882,f886])).

fof(f886,plain,
    ( ~ spl4_44
    | spl4_45 ),
    inference(avatar_contradiction_clause,[],[f885])).

fof(f885,plain,
    ( $false
    | ~ spl4_44
    | spl4_45 ),
    inference(subsumption_resolution,[],[f883,f881])).

fof(f881,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | spl4_45 ),
    inference(avatar_component_clause,[],[f879])).

fof(f879,plain,
    ( spl4_45
  <=> l1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f883,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f876,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f876,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f874])).

fof(f874,plain,
    ( spl4_44
  <=> l1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f882,plain,
    ( ~ spl4_45
    | spl4_1
    | ~ spl4_4
    | spl4_8
    | ~ spl4_21
    | spl4_34
    | ~ spl4_35
    | ~ spl4_38
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f870,f859,f629,f600,f595,f343,f137,f118,f103,f879])).

fof(f103,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f118,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f137,plain,
    ( spl4_8
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f343,plain,
    ( spl4_21
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f595,plain,
    ( spl4_34
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f600,plain,
    ( spl4_35
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f629,plain,
    ( spl4_38
  <=> v2_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f859,plain,
    ( spl4_43
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f870,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_4
    | spl4_8
    | ~ spl4_21
    | spl4_34
    | ~ spl4_35
    | ~ spl4_38
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f867,f868])).

fof(f868,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_21
    | spl4_34
    | ~ spl4_35
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f105,f120,f602,f597,f345,f630,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | ~ v2_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_tdlat_3(X1)
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_tdlat_3(X1)
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_tdlat_3(X1)
              & ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc23_tex_2)).

fof(f630,plain,
    ( v2_tdlat_3(sK2(sK0,sK1))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f629])).

fof(f345,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f343])).

fof(f597,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | spl4_34 ),
    inference(avatar_component_clause,[],[f595])).

fof(f602,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f600])).

fof(f120,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f118])).

fof(f105,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f867,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | spl4_8
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f864,f138])).

fof(f138,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f864,plain,
    ( v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ spl4_43 ),
    inference(superposition,[],[f84,f861])).

fof(f861,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f859])).

fof(f84,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f877,plain,
    ( spl4_44
    | ~ spl4_4
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f846,f600,f118,f874])).

fof(f846,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_35 ),
    inference(unit_resulting_resolution,[],[f120,f602,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f862,plain,
    ( spl4_43
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f839,f133,f128,f123,f118,f108,f103,f859])).

fof(f108,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f123,plain,
    ( spl4_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f128,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f133,plain,
    ( spl4_7
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f839,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f105,f110,f120,f125,f130,f135,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(sK2(X0,X1)) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_tdlat_3(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_tdlat_3(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f135,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f130,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f125,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f110,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f812,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_25
    | spl4_35
    | ~ spl4_41 ),
    inference(avatar_contradiction_clause,[],[f811])).

fof(f811,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_25
    | spl4_35
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f810,f130])).

fof(f810,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_22
    | ~ spl4_25
    | spl4_35
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f809,f484])).

fof(f484,plain,
    ( sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | ~ spl4_22
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f478,f350])).

fof(f350,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl4_22
  <=> sK1 = k1_tarski(sK3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f478,plain,
    ( k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1))
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f468,f170])).

fof(f170,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(subsumption_resolution,[],[f168,f87])).

fof(f87,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f168,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f90,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f468,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl4_25
  <=> r2_hidden(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f809,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_22
    | ~ spl4_25
    | spl4_35
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f808,f601])).

fof(f601,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl4_35 ),
    inference(avatar_component_clause,[],[f600])).

fof(f808,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_22
    | ~ spl4_25
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f807,f484])).

fof(f807,plain,
    ( m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK1))),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_22
    | ~ spl4_25
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f806,f125])).

fof(f806,plain,
    ( v1_xboole_0(sK1)
    | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK1))),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_22
    | ~ spl4_25
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f794,f484])).

fof(f794,plain,
    ( v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK3(sK1)))
    | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK1))),sK0)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_41 ),
    inference(resolution,[],[f773,f246])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(k6_domain_1(u1_struct_0(sK0),X0))
        | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK0)
        | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f245,f105])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k6_domain_1(u1_struct_0(sK0),X0))
        | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f244,f110])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k6_domain_1(u1_struct_0(sK0),X0))
        | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f243,f120])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(k6_domain_1(u1_struct_0(sK0),X0))
        | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(resolution,[],[f185,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

% (16915)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f185,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | m1_pre_topc(sK2(sK0,X0),sK0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f184,f105])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | m1_pre_topc(sK2(sK0,X0),sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f183,f120])).

fof(f183,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ l1_pre_topc(sK0)
        | m1_pre_topc(sK2(sK0,X0),sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f80,f110])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(sK2(X0,X1),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f773,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f771])).

fof(f771,plain,
    ( spl4_41
  <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f800,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_7
    | ~ spl4_22
    | ~ spl4_25
    | ~ spl4_41 ),
    inference(avatar_contradiction_clause,[],[f799])).

fof(f799,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_7
    | ~ spl4_22
    | ~ spl4_25
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f798,f134])).

fof(f134,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f798,plain,
    ( v2_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_22
    | ~ spl4_25
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f791,f484])).

fof(f791,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_41 ),
    inference(unit_resulting_resolution,[],[f105,f110,f120,f773,f77])).

fof(f774,plain,
    ( spl4_41
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f475,f466,f771])).

fof(f475,plain,
    ( m1_subset_1(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_25 ),
    inference(unit_resulting_resolution,[],[f468,f89])).

fof(f636,plain,
    ( ~ spl4_35
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_38 ),
    inference(avatar_split_clause,[],[f633,f629,f118,f113,f103,f600])).

fof(f113,plain,
    ( spl4_3
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f633,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_38 ),
    inference(unit_resulting_resolution,[],[f105,f115,f120,f631,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f76,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f631,plain,
    ( ~ v2_tdlat_3(sK2(sK0,sK1))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f629])).

fof(f115,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f610,plain,
    ( ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f605,f137,f133])).

fof(f605,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f70,f139])).

fof(f139,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f137])).

fof(f70,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v2_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v2_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f603,plain,
    ( spl4_35
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f586,f133,f128,f123,f118,f108,f103,f600])).

fof(f586,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f105,f110,f120,f125,f130,f135,f80])).

fof(f598,plain,
    ( ~ spl4_34
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f588,f133,f128,f123,f118,f108,f103,f595])).

fof(f588,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f105,f110,f120,f125,f130,f135,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f469,plain,
    ( spl4_25
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f368,f293,f466])).

fof(f293,plain,
    ( spl4_16
  <=> r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f368,plain,
    ( r2_hidden(sK3(sK1),u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f295,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f295,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f293])).

fof(f445,plain,
    ( spl4_22
    | spl4_5
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f353,f267,f137,f123,f348])).

fof(f267,plain,
    ( spl4_15
  <=> r1_tarski(k1_tarski(sK3(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f353,plain,
    ( sK1 = k1_tarski(sK3(sK1))
    | spl4_5
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f125,f71,f269,f139,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f269,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f267])).

fof(f71,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f346,plain,
    ( spl4_21
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f337,f133,f128,f123,f118,f108,f103,f343])).

fof(f337,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f105,f110,f120,f125,f130,f135,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v1_tdlat_3(sK2(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f296,plain,
    ( spl4_16
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f250,f190,f176,f293])).

fof(f176,plain,
    ( spl4_10
  <=> r2_hidden(sK3(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f190,plain,
    ( spl4_11
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f250,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0))
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f178,f192,f166])).

fof(f166,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k1_tarski(X4),X3)
      | ~ r2_hidden(X4,X2) ) ),
    inference(resolution,[],[f98,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f192,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f190])).

fof(f178,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f176])).

fof(f270,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f194,f176,f267])).

fof(f194,plain,
    ( r1_tarski(k1_tarski(sK3(sK1)),sK1)
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f178,f95])).

fof(f193,plain,
    ( spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f156,f128,f190])).

fof(f156,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f130,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f179,plain,
    ( spl4_10
    | spl4_5 ),
    inference(avatar_split_clause,[],[f151,f123,f176])).

fof(f151,plain,
    ( r2_hidden(sK3(sK1),sK1)
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f125,f88])).

fof(f88,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f140,plain,
    ( spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f69,f137,f133])).

fof(f69,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f131,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f68,f128])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f126,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f67,f123])).

fof(f67,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f121,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f66,f118])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f116,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f65,f113])).

fof(f65,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f111,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f64,f108])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f63,f103])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:23:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (16893)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (16898)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (16895)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (16909)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (16894)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (16896)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (16895)Refutation not found, incomplete strategy% (16895)------------------------------
% 0.21/0.51  % (16895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16895)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16895)Memory used [KB]: 6140
% 0.21/0.51  % (16895)Time elapsed: 0.064 s
% 0.21/0.51  % (16895)------------------------------
% 0.21/0.51  % (16895)------------------------------
% 0.21/0.51  % (16890)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (16901)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (16903)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (16913)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (16904)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (16914)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (16902)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (16905)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (16892)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (16911)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (16912)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (16907)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (16910)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.32/0.53  % (16890)Refutation not found, incomplete strategy% (16890)------------------------------
% 1.32/0.53  % (16890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (16890)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (16890)Memory used [KB]: 10618
% 1.32/0.53  % (16890)Time elapsed: 0.112 s
% 1.32/0.53  % (16890)------------------------------
% 1.32/0.53  % (16890)------------------------------
% 1.32/0.53  % (16896)Refutation not found, incomplete strategy% (16896)------------------------------
% 1.32/0.53  % (16896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (16896)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (16896)Memory used [KB]: 10618
% 1.32/0.53  % (16896)Time elapsed: 0.118 s
% 1.32/0.53  % (16896)------------------------------
% 1.32/0.53  % (16896)------------------------------
% 1.32/0.53  % (16900)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.32/0.53  % (16891)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.53  % (16906)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.32/0.53  % (16899)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.32/0.54  % (16913)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % (16908)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.47/0.55  % SZS output start Proof for theBenchmark
% 1.47/0.55  fof(f887,plain,(
% 1.47/0.55    $false),
% 1.47/0.55    inference(avatar_sat_refutation,[],[f106,f111,f116,f121,f126,f131,f140,f179,f193,f270,f296,f346,f445,f469,f598,f603,f610,f636,f774,f800,f812,f862,f877,f882,f886])).
% 1.47/0.55  fof(f886,plain,(
% 1.47/0.55    ~spl4_44 | spl4_45),
% 1.47/0.55    inference(avatar_contradiction_clause,[],[f885])).
% 1.47/0.55  fof(f885,plain,(
% 1.47/0.55    $false | (~spl4_44 | spl4_45)),
% 1.47/0.55    inference(subsumption_resolution,[],[f883,f881])).
% 1.47/0.55  fof(f881,plain,(
% 1.47/0.55    ~l1_struct_0(sK2(sK0,sK1)) | spl4_45),
% 1.47/0.55    inference(avatar_component_clause,[],[f879])).
% 1.47/0.55  fof(f879,plain,(
% 1.47/0.55    spl4_45 <=> l1_struct_0(sK2(sK0,sK1))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.47/0.55  fof(f883,plain,(
% 1.47/0.55    l1_struct_0(sK2(sK0,sK1)) | ~spl4_44),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f876,f73])).
% 1.47/0.55  fof(f73,plain,(
% 1.47/0.55    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f26])).
% 1.47/0.55  fof(f26,plain,(
% 1.47/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f8])).
% 1.47/0.55  fof(f8,axiom,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.47/0.55  fof(f876,plain,(
% 1.47/0.55    l1_pre_topc(sK2(sK0,sK1)) | ~spl4_44),
% 1.47/0.55    inference(avatar_component_clause,[],[f874])).
% 1.47/0.55  fof(f874,plain,(
% 1.47/0.55    spl4_44 <=> l1_pre_topc(sK2(sK0,sK1))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.47/0.55  fof(f882,plain,(
% 1.47/0.55    ~spl4_45 | spl4_1 | ~spl4_4 | spl4_8 | ~spl4_21 | spl4_34 | ~spl4_35 | ~spl4_38 | ~spl4_43),
% 1.47/0.55    inference(avatar_split_clause,[],[f870,f859,f629,f600,f595,f343,f137,f118,f103,f879])).
% 1.47/0.55  fof(f103,plain,(
% 1.47/0.55    spl4_1 <=> v2_struct_0(sK0)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.47/0.55  fof(f118,plain,(
% 1.47/0.55    spl4_4 <=> l1_pre_topc(sK0)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.47/0.55  fof(f137,plain,(
% 1.47/0.55    spl4_8 <=> v1_zfmisc_1(sK1)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.47/0.55  fof(f343,plain,(
% 1.47/0.55    spl4_21 <=> v1_tdlat_3(sK2(sK0,sK1))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.47/0.55  fof(f595,plain,(
% 1.47/0.55    spl4_34 <=> v2_struct_0(sK2(sK0,sK1))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.47/0.55  fof(f600,plain,(
% 1.47/0.55    spl4_35 <=> m1_pre_topc(sK2(sK0,sK1),sK0)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.47/0.55  fof(f629,plain,(
% 1.47/0.55    spl4_38 <=> v2_tdlat_3(sK2(sK0,sK1))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.47/0.55  fof(f859,plain,(
% 1.47/0.55    spl4_43 <=> sK1 = u1_struct_0(sK2(sK0,sK1))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.47/0.55  fof(f870,plain,(
% 1.47/0.55    ~l1_struct_0(sK2(sK0,sK1)) | (spl4_1 | ~spl4_4 | spl4_8 | ~spl4_21 | spl4_34 | ~spl4_35 | ~spl4_38 | ~spl4_43)),
% 1.47/0.55    inference(subsumption_resolution,[],[f867,f868])).
% 1.47/0.55  fof(f868,plain,(
% 1.47/0.55    v7_struct_0(sK2(sK0,sK1)) | (spl4_1 | ~spl4_4 | ~spl4_21 | spl4_34 | ~spl4_35 | ~spl4_38)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f105,f120,f602,f597,f345,f630,f83])).
% 1.47/0.55  fof(f83,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~v1_tdlat_3(X1) | ~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f37])).
% 1.47/0.55  fof(f37,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.55    inference(flattening,[],[f36])).
% 1.47/0.55  fof(f36,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f13])).
% 1.47/0.55  fof(f13,axiom,(
% 1.47/0.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_tdlat_3(X1) & ~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc23_tex_2)).
% 1.47/0.55  fof(f630,plain,(
% 1.47/0.55    v2_tdlat_3(sK2(sK0,sK1)) | ~spl4_38),
% 1.47/0.55    inference(avatar_component_clause,[],[f629])).
% 1.47/0.55  fof(f345,plain,(
% 1.47/0.55    v1_tdlat_3(sK2(sK0,sK1)) | ~spl4_21),
% 1.47/0.55    inference(avatar_component_clause,[],[f343])).
% 1.47/0.55  fof(f597,plain,(
% 1.47/0.55    ~v2_struct_0(sK2(sK0,sK1)) | spl4_34),
% 1.47/0.55    inference(avatar_component_clause,[],[f595])).
% 1.47/0.55  fof(f602,plain,(
% 1.47/0.55    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl4_35),
% 1.47/0.55    inference(avatar_component_clause,[],[f600])).
% 1.47/0.55  fof(f120,plain,(
% 1.47/0.55    l1_pre_topc(sK0) | ~spl4_4),
% 1.47/0.55    inference(avatar_component_clause,[],[f118])).
% 1.47/0.55  fof(f105,plain,(
% 1.47/0.55    ~v2_struct_0(sK0) | spl4_1),
% 1.47/0.55    inference(avatar_component_clause,[],[f103])).
% 1.47/0.55  fof(f867,plain,(
% 1.47/0.55    ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | (spl4_8 | ~spl4_43)),
% 1.47/0.55    inference(subsumption_resolution,[],[f864,f138])).
% 1.47/0.55  fof(f138,plain,(
% 1.47/0.55    ~v1_zfmisc_1(sK1) | spl4_8),
% 1.47/0.55    inference(avatar_component_clause,[],[f137])).
% 1.47/0.55  fof(f864,plain,(
% 1.47/0.55    v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | ~spl4_43),
% 1.47/0.55    inference(superposition,[],[f84,f861])).
% 1.47/0.55  fof(f861,plain,(
% 1.47/0.55    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl4_43),
% 1.47/0.55    inference(avatar_component_clause,[],[f859])).
% 1.47/0.55  fof(f84,plain,(
% 1.47/0.55    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f39])).
% 1.47/0.55  fof(f39,plain,(
% 1.47/0.55    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.47/0.55    inference(flattening,[],[f38])).
% 1.47/0.55  fof(f38,plain,(
% 1.47/0.55    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f10])).
% 1.47/0.55  fof(f10,axiom,(
% 1.47/0.55    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.47/0.55  fof(f877,plain,(
% 1.47/0.55    spl4_44 | ~spl4_4 | ~spl4_35),
% 1.47/0.55    inference(avatar_split_clause,[],[f846,f600,f118,f874])).
% 1.47/0.55  fof(f846,plain,(
% 1.47/0.55    l1_pre_topc(sK2(sK0,sK1)) | (~spl4_4 | ~spl4_35)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f120,f602,f75])).
% 1.47/0.55  fof(f75,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f29])).
% 1.47/0.55  fof(f29,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f9])).
% 1.47/0.55  fof(f9,axiom,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.47/0.55  fof(f862,plain,(
% 1.47/0.55    spl4_43 | spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7),
% 1.47/0.55    inference(avatar_split_clause,[],[f839,f133,f128,f123,f118,f108,f103,f859])).
% 1.47/0.55  fof(f108,plain,(
% 1.47/0.55    spl4_2 <=> v2_pre_topc(sK0)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.47/0.55  fof(f123,plain,(
% 1.47/0.55    spl4_5 <=> v1_xboole_0(sK1)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.47/0.55  fof(f128,plain,(
% 1.47/0.55    spl4_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.47/0.55  fof(f133,plain,(
% 1.47/0.55    spl4_7 <=> v2_tex_2(sK1,sK0)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.47/0.55  fof(f839,plain,(
% 1.47/0.55    sK1 = u1_struct_0(sK2(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f105,f110,f120,f125,f130,f135,f81])).
% 1.47/0.55  fof(f81,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | u1_struct_0(sK2(X0,X1)) = X1 | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f53])).
% 1.47/0.55  fof(f53,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : ((u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f52])).
% 1.47/0.55  fof(f52,plain,(
% 1.47/0.55    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK2(X0,X1)) = X1 & m1_pre_topc(sK2(X0,X1),X0) & v1_tdlat_3(sK2(X0,X1)) & ~v2_struct_0(sK2(X0,X1))))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f35,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.55    inference(flattening,[],[f34])).
% 1.47/0.55  fof(f34,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f21])).
% 1.47/0.55  fof(f21,plain,(
% 1.47/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.47/0.55    inference(pure_predicate_removal,[],[f17])).
% 1.47/0.55  fof(f17,axiom,(
% 1.47/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 1.47/0.55  fof(f135,plain,(
% 1.47/0.55    v2_tex_2(sK1,sK0) | ~spl4_7),
% 1.47/0.55    inference(avatar_component_clause,[],[f133])).
% 1.47/0.55  fof(f130,plain,(
% 1.47/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 1.47/0.55    inference(avatar_component_clause,[],[f128])).
% 1.47/0.55  fof(f125,plain,(
% 1.47/0.55    ~v1_xboole_0(sK1) | spl4_5),
% 1.47/0.55    inference(avatar_component_clause,[],[f123])).
% 1.47/0.55  fof(f110,plain,(
% 1.47/0.55    v2_pre_topc(sK0) | ~spl4_2),
% 1.47/0.55    inference(avatar_component_clause,[],[f108])).
% 1.47/0.55  fof(f812,plain,(
% 1.47/0.55    spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_22 | ~spl4_25 | spl4_35 | ~spl4_41),
% 1.47/0.55    inference(avatar_contradiction_clause,[],[f811])).
% 1.47/0.55  fof(f811,plain,(
% 1.47/0.55    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_22 | ~spl4_25 | spl4_35 | ~spl4_41)),
% 1.47/0.55    inference(subsumption_resolution,[],[f810,f130])).
% 1.47/0.55  fof(f810,plain,(
% 1.47/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_22 | ~spl4_25 | spl4_35 | ~spl4_41)),
% 1.47/0.55    inference(forward_demodulation,[],[f809,f484])).
% 1.47/0.55  fof(f484,plain,(
% 1.47/0.55    sK1 = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | (~spl4_22 | ~spl4_25)),
% 1.47/0.55    inference(forward_demodulation,[],[f478,f350])).
% 1.47/0.55  fof(f350,plain,(
% 1.47/0.55    sK1 = k1_tarski(sK3(sK1)) | ~spl4_22),
% 1.47/0.55    inference(avatar_component_clause,[],[f348])).
% 1.47/0.55  fof(f348,plain,(
% 1.47/0.55    spl4_22 <=> sK1 = k1_tarski(sK3(sK1))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.47/0.55  fof(f478,plain,(
% 1.47/0.55    k1_tarski(sK3(sK1)) = k6_domain_1(u1_struct_0(sK0),sK3(sK1)) | ~spl4_25),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f468,f170])).
% 1.47/0.55  fof(f170,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f168,f87])).
% 1.47/0.55  fof(f87,plain,(
% 1.47/0.55    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f58])).
% 1.47/0.55  fof(f58,plain,(
% 1.47/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f56,f57])).
% 1.47/0.55  fof(f57,plain,(
% 1.47/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f56,plain,(
% 1.47/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.55    inference(rectify,[],[f55])).
% 1.47/0.55  fof(f55,plain,(
% 1.47/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.47/0.55    inference(nnf_transformation,[],[f1])).
% 1.47/0.55  fof(f1,axiom,(
% 1.47/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.47/0.55  fof(f168,plain,(
% 1.47/0.55    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.47/0.55    inference(resolution,[],[f90,f89])).
% 1.47/0.55  fof(f89,plain,(
% 1.47/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f42])).
% 1.47/0.55  fof(f42,plain,(
% 1.47/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.47/0.55    inference(ennf_transformation,[],[f6])).
% 1.47/0.55  fof(f6,axiom,(
% 1.47/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.47/0.55  fof(f90,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f44])).
% 1.47/0.55  fof(f44,plain,(
% 1.47/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.47/0.55    inference(flattening,[],[f43])).
% 1.47/0.55  fof(f43,plain,(
% 1.47/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f11])).
% 1.47/0.55  fof(f11,axiom,(
% 1.47/0.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.47/0.55  fof(f468,plain,(
% 1.47/0.55    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | ~spl4_25),
% 1.47/0.55    inference(avatar_component_clause,[],[f466])).
% 1.47/0.55  fof(f466,plain,(
% 1.47/0.55    spl4_25 <=> r2_hidden(sK3(sK1),u1_struct_0(sK0))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.47/0.55  fof(f809,plain,(
% 1.47/0.55    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_22 | ~spl4_25 | spl4_35 | ~spl4_41)),
% 1.47/0.55    inference(subsumption_resolution,[],[f808,f601])).
% 1.47/0.55  fof(f601,plain,(
% 1.47/0.55    ~m1_pre_topc(sK2(sK0,sK1),sK0) | spl4_35),
% 1.47/0.55    inference(avatar_component_clause,[],[f600])).
% 1.47/0.55  fof(f808,plain,(
% 1.47/0.55    m1_pre_topc(sK2(sK0,sK1),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_22 | ~spl4_25 | ~spl4_41)),
% 1.47/0.55    inference(forward_demodulation,[],[f807,f484])).
% 1.47/0.55  fof(f807,plain,(
% 1.47/0.55    m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK1))),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_22 | ~spl4_25 | ~spl4_41)),
% 1.47/0.55    inference(subsumption_resolution,[],[f806,f125])).
% 1.47/0.55  fof(f806,plain,(
% 1.47/0.55    v1_xboole_0(sK1) | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK1))),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_22 | ~spl4_25 | ~spl4_41)),
% 1.47/0.55    inference(forward_demodulation,[],[f794,f484])).
% 1.47/0.55  fof(f794,plain,(
% 1.47/0.55    v1_xboole_0(k6_domain_1(u1_struct_0(sK0),sK3(sK1))) | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),sK3(sK1))),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_41)),
% 1.47/0.55    inference(resolution,[],[f773,f246])).
% 1.47/0.55  fof(f246,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(k6_domain_1(u1_struct_0(sK0),X0)) | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK0) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 1.47/0.55    inference(subsumption_resolution,[],[f245,f105])).
% 1.47/0.55  fof(f245,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k6_domain_1(u1_struct_0(sK0),X0)) | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 1.47/0.55    inference(subsumption_resolution,[],[f244,f110])).
% 1.47/0.55  fof(f244,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k6_domain_1(u1_struct_0(sK0),X0)) | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 1.47/0.55    inference(subsumption_resolution,[],[f243,f120])).
% 1.47/0.55  fof(f243,plain,(
% 1.47/0.55    ( ! [X0] : (~m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k6_domain_1(u1_struct_0(sK0),X0)) | m1_pre_topc(sK2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 1.47/0.55    inference(resolution,[],[f185,f77])).
% 1.47/0.55  fof(f77,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f33])).
% 1.47/0.55  fof(f33,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.55    inference(flattening,[],[f32])).
% 1.47/0.55  % (16915)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.47/0.55  fof(f32,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f18])).
% 1.47/0.55  fof(f18,axiom,(
% 1.47/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 1.47/0.55  fof(f185,plain,(
% 1.47/0.55    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | m1_pre_topc(sK2(sK0,X0),sK0)) ) | (spl4_1 | ~spl4_2 | ~spl4_4)),
% 1.47/0.55    inference(subsumption_resolution,[],[f184,f105])).
% 1.47/0.55  fof(f184,plain,(
% 1.47/0.55    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | m1_pre_topc(sK2(sK0,X0),sK0) | v2_struct_0(sK0)) ) | (~spl4_2 | ~spl4_4)),
% 1.47/0.55    inference(subsumption_resolution,[],[f183,f120])).
% 1.47/0.55  fof(f183,plain,(
% 1.47/0.55    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | m1_pre_topc(sK2(sK0,X0),sK0) | v2_struct_0(sK0)) ) | ~spl4_2),
% 1.47/0.55    inference(resolution,[],[f80,f110])).
% 1.47/0.55  fof(f80,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | m1_pre_topc(sK2(X0,X1),X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f53])).
% 1.47/0.55  fof(f773,plain,(
% 1.47/0.55    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl4_41),
% 1.47/0.55    inference(avatar_component_clause,[],[f771])).
% 1.47/0.55  fof(f771,plain,(
% 1.47/0.55    spl4_41 <=> m1_subset_1(sK3(sK1),u1_struct_0(sK0))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.47/0.55  fof(f800,plain,(
% 1.47/0.55    spl4_1 | ~spl4_2 | ~spl4_4 | spl4_7 | ~spl4_22 | ~spl4_25 | ~spl4_41),
% 1.47/0.55    inference(avatar_contradiction_clause,[],[f799])).
% 1.47/0.55  fof(f799,plain,(
% 1.47/0.55    $false | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_7 | ~spl4_22 | ~spl4_25 | ~spl4_41)),
% 1.47/0.55    inference(subsumption_resolution,[],[f798,f134])).
% 1.47/0.55  fof(f134,plain,(
% 1.47/0.55    ~v2_tex_2(sK1,sK0) | spl4_7),
% 1.47/0.55    inference(avatar_component_clause,[],[f133])).
% 1.47/0.55  fof(f798,plain,(
% 1.47/0.55    v2_tex_2(sK1,sK0) | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_22 | ~spl4_25 | ~spl4_41)),
% 1.47/0.55    inference(forward_demodulation,[],[f791,f484])).
% 1.47/0.55  fof(f791,plain,(
% 1.47/0.55    v2_tex_2(k6_domain_1(u1_struct_0(sK0),sK3(sK1)),sK0) | (spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_41)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f105,f110,f120,f773,f77])).
% 1.47/0.55  fof(f774,plain,(
% 1.47/0.55    spl4_41 | ~spl4_25),
% 1.47/0.55    inference(avatar_split_clause,[],[f475,f466,f771])).
% 1.47/0.55  fof(f475,plain,(
% 1.47/0.55    m1_subset_1(sK3(sK1),u1_struct_0(sK0)) | ~spl4_25),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f468,f89])).
% 1.47/0.55  fof(f636,plain,(
% 1.47/0.55    ~spl4_35 | spl4_1 | ~spl4_3 | ~spl4_4 | spl4_38),
% 1.47/0.55    inference(avatar_split_clause,[],[f633,f629,f118,f113,f103,f600])).
% 1.47/0.55  fof(f113,plain,(
% 1.47/0.55    spl4_3 <=> v2_tdlat_3(sK0)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.47/0.55  fof(f633,plain,(
% 1.47/0.55    ~m1_pre_topc(sK2(sK0,sK1),sK0) | (spl4_1 | ~spl4_3 | ~spl4_4 | spl4_38)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f105,f115,f120,f631,f101])).
% 1.47/0.55  fof(f101,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_tdlat_3(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(subsumption_resolution,[],[f76,f74])).
% 1.47/0.55  fof(f74,plain,(
% 1.47/0.55    ( ! [X0] : (~v2_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f28])).
% 1.47/0.55  fof(f28,plain,(
% 1.47/0.55    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(flattening,[],[f27])).
% 1.47/0.55  fof(f27,plain,(
% 1.47/0.55    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f14])).
% 1.47/0.55  fof(f14,axiom,(
% 1.47/0.55    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.47/0.55  fof(f76,plain,(
% 1.47/0.55    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f31])).
% 1.47/0.55  fof(f31,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.55    inference(flattening,[],[f30])).
% 1.47/0.55  fof(f30,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f15])).
% 1.47/0.55  fof(f15,axiom,(
% 1.47/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 1.47/0.55  fof(f631,plain,(
% 1.47/0.55    ~v2_tdlat_3(sK2(sK0,sK1)) | spl4_38),
% 1.47/0.55    inference(avatar_component_clause,[],[f629])).
% 1.47/0.55  fof(f115,plain,(
% 1.47/0.55    v2_tdlat_3(sK0) | ~spl4_3),
% 1.47/0.55    inference(avatar_component_clause,[],[f113])).
% 1.47/0.55  fof(f610,plain,(
% 1.47/0.55    ~spl4_7 | ~spl4_8),
% 1.47/0.55    inference(avatar_split_clause,[],[f605,f137,f133])).
% 1.47/0.55  fof(f605,plain,(
% 1.47/0.55    ~v2_tex_2(sK1,sK0) | ~spl4_8),
% 1.47/0.55    inference(subsumption_resolution,[],[f70,f139])).
% 1.47/0.55  fof(f139,plain,(
% 1.47/0.55    v1_zfmisc_1(sK1) | ~spl4_8),
% 1.47/0.55    inference(avatar_component_clause,[],[f137])).
% 1.47/0.55  fof(f70,plain,(
% 1.47/0.55    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f51])).
% 1.47/0.55  fof(f51,plain,(
% 1.47/0.55    ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.47/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).
% 1.47/0.55  fof(f49,plain,(
% 1.47/0.55    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f50,plain,(
% 1.47/0.55    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 1.47/0.55    introduced(choice_axiom,[])).
% 1.47/0.55  fof(f48,plain,(
% 1.47/0.55    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.55    inference(flattening,[],[f47])).
% 1.47/0.55  fof(f47,plain,(
% 1.47/0.55    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.55    inference(nnf_transformation,[],[f23])).
% 1.47/0.55  fof(f23,plain,(
% 1.47/0.55    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.55    inference(flattening,[],[f22])).
% 1.47/0.55  fof(f22,plain,(
% 1.47/0.55    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.47/0.55    inference(ennf_transformation,[],[f20])).
% 1.47/0.55  fof(f20,negated_conjecture,(
% 1.47/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.47/0.55    inference(negated_conjecture,[],[f19])).
% 1.47/0.55  fof(f19,conjecture,(
% 1.47/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 1.47/0.55  fof(f603,plain,(
% 1.47/0.55    spl4_35 | spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7),
% 1.47/0.55    inference(avatar_split_clause,[],[f586,f133,f128,f123,f118,f108,f103,f600])).
% 1.47/0.55  fof(f586,plain,(
% 1.47/0.55    m1_pre_topc(sK2(sK0,sK1),sK0) | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f105,f110,f120,f125,f130,f135,f80])).
% 1.47/0.55  fof(f598,plain,(
% 1.47/0.55    ~spl4_34 | spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7),
% 1.47/0.55    inference(avatar_split_clause,[],[f588,f133,f128,f123,f118,f108,f103,f595])).
% 1.47/0.55  fof(f588,plain,(
% 1.47/0.55    ~v2_struct_0(sK2(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f105,f110,f120,f125,f130,f135,f78])).
% 1.47/0.55  fof(f78,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f53])).
% 1.47/0.55  fof(f469,plain,(
% 1.47/0.55    spl4_25 | ~spl4_16),
% 1.47/0.55    inference(avatar_split_clause,[],[f368,f293,f466])).
% 1.47/0.55  fof(f293,plain,(
% 1.47/0.55    spl4_16 <=> r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.47/0.55  fof(f368,plain,(
% 1.47/0.55    r2_hidden(sK3(sK1),u1_struct_0(sK0)) | ~spl4_16),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f295,f94])).
% 1.47/0.55  fof(f94,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f61])).
% 1.47/0.55  fof(f61,plain,(
% 1.47/0.55    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.47/0.55    inference(nnf_transformation,[],[f5])).
% 1.47/0.55  fof(f5,axiom,(
% 1.47/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.47/0.55  fof(f295,plain,(
% 1.47/0.55    r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0)) | ~spl4_16),
% 1.47/0.55    inference(avatar_component_clause,[],[f293])).
% 1.47/0.55  fof(f445,plain,(
% 1.47/0.55    spl4_22 | spl4_5 | ~spl4_8 | ~spl4_15),
% 1.47/0.55    inference(avatar_split_clause,[],[f353,f267,f137,f123,f348])).
% 1.47/0.55  fof(f267,plain,(
% 1.47/0.55    spl4_15 <=> r1_tarski(k1_tarski(sK3(sK1)),sK1)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.47/0.55  fof(f353,plain,(
% 1.47/0.55    sK1 = k1_tarski(sK3(sK1)) | (spl4_5 | ~spl4_8 | ~spl4_15)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f125,f71,f269,f139,f72])).
% 1.47/0.55  fof(f72,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f25])).
% 1.47/0.55  fof(f25,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.47/0.55    inference(flattening,[],[f24])).
% 1.47/0.55  fof(f24,plain,(
% 1.47/0.55    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.47/0.55    inference(ennf_transformation,[],[f16])).
% 1.47/0.55  fof(f16,axiom,(
% 1.47/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.47/0.55  fof(f269,plain,(
% 1.47/0.55    r1_tarski(k1_tarski(sK3(sK1)),sK1) | ~spl4_15),
% 1.47/0.55    inference(avatar_component_clause,[],[f267])).
% 1.47/0.55  fof(f71,plain,(
% 1.47/0.55    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.47/0.55    inference(cnf_transformation,[],[f4])).
% 1.47/0.55  fof(f4,axiom,(
% 1.47/0.55    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.47/0.55  fof(f346,plain,(
% 1.47/0.55    spl4_21 | spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7),
% 1.47/0.55    inference(avatar_split_clause,[],[f337,f133,f128,f123,f118,f108,f103,f343])).
% 1.47/0.55  fof(f337,plain,(
% 1.47/0.55    v1_tdlat_3(sK2(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_7)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f105,f110,f120,f125,f130,f135,f79])).
% 1.47/0.55  fof(f79,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v1_tdlat_3(sK2(X0,X1)) | v2_struct_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f53])).
% 1.47/0.55  fof(f296,plain,(
% 1.47/0.55    spl4_16 | ~spl4_10 | ~spl4_11),
% 1.47/0.55    inference(avatar_split_clause,[],[f250,f190,f176,f293])).
% 1.47/0.55  fof(f176,plain,(
% 1.47/0.55    spl4_10 <=> r2_hidden(sK3(sK1),sK1)),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.47/0.55  fof(f190,plain,(
% 1.47/0.55    spl4_11 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.47/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.47/0.55  fof(f250,plain,(
% 1.47/0.55    r1_tarski(k1_tarski(sK3(sK1)),u1_struct_0(sK0)) | (~spl4_10 | ~spl4_11)),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f178,f192,f166])).
% 1.47/0.55  fof(f166,plain,(
% 1.47/0.55    ( ! [X4,X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k1_tarski(X4),X3) | ~r2_hidden(X4,X2)) )),
% 1.47/0.55    inference(resolution,[],[f98,f95])).
% 1.47/0.55  fof(f95,plain,(
% 1.47/0.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f61])).
% 1.47/0.55  fof(f98,plain,(
% 1.47/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f46])).
% 1.47/0.55  fof(f46,plain,(
% 1.47/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.47/0.55    inference(flattening,[],[f45])).
% 1.47/0.55  fof(f45,plain,(
% 1.47/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.47/0.55    inference(ennf_transformation,[],[f3])).
% 1.47/0.55  fof(f3,axiom,(
% 1.47/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.47/0.55  fof(f192,plain,(
% 1.47/0.55    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_11),
% 1.47/0.55    inference(avatar_component_clause,[],[f190])).
% 1.47/0.55  fof(f178,plain,(
% 1.47/0.55    r2_hidden(sK3(sK1),sK1) | ~spl4_10),
% 1.47/0.55    inference(avatar_component_clause,[],[f176])).
% 1.47/0.55  fof(f270,plain,(
% 1.47/0.55    spl4_15 | ~spl4_10),
% 1.47/0.55    inference(avatar_split_clause,[],[f194,f176,f267])).
% 1.47/0.55  fof(f194,plain,(
% 1.47/0.55    r1_tarski(k1_tarski(sK3(sK1)),sK1) | ~spl4_10),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f178,f95])).
% 1.47/0.55  fof(f193,plain,(
% 1.47/0.55    spl4_11 | ~spl4_6),
% 1.47/0.55    inference(avatar_split_clause,[],[f156,f128,f190])).
% 1.47/0.55  fof(f156,plain,(
% 1.47/0.55    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl4_6),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f130,f96])).
% 1.47/0.55  fof(f96,plain,(
% 1.47/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f62])).
% 1.47/0.55  fof(f62,plain,(
% 1.47/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.47/0.55    inference(nnf_transformation,[],[f7])).
% 1.47/0.55  fof(f7,axiom,(
% 1.47/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.47/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.47/0.55  fof(f179,plain,(
% 1.47/0.55    spl4_10 | spl4_5),
% 1.47/0.55    inference(avatar_split_clause,[],[f151,f123,f176])).
% 1.47/0.55  fof(f151,plain,(
% 1.47/0.55    r2_hidden(sK3(sK1),sK1) | spl4_5),
% 1.47/0.55    inference(unit_resulting_resolution,[],[f125,f88])).
% 1.47/0.55  fof(f88,plain,(
% 1.47/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.47/0.55    inference(cnf_transformation,[],[f58])).
% 1.47/0.55  fof(f140,plain,(
% 1.47/0.55    spl4_7 | spl4_8),
% 1.47/0.55    inference(avatar_split_clause,[],[f69,f137,f133])).
% 1.47/0.55  fof(f69,plain,(
% 1.47/0.55    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f51])).
% 1.47/0.55  fof(f131,plain,(
% 1.47/0.55    spl4_6),
% 1.47/0.55    inference(avatar_split_clause,[],[f68,f128])).
% 1.47/0.55  fof(f68,plain,(
% 1.47/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.55    inference(cnf_transformation,[],[f51])).
% 1.47/0.55  fof(f126,plain,(
% 1.47/0.55    ~spl4_5),
% 1.47/0.55    inference(avatar_split_clause,[],[f67,f123])).
% 1.47/0.55  fof(f67,plain,(
% 1.47/0.55    ~v1_xboole_0(sK1)),
% 1.47/0.55    inference(cnf_transformation,[],[f51])).
% 1.47/0.55  fof(f121,plain,(
% 1.47/0.55    spl4_4),
% 1.47/0.55    inference(avatar_split_clause,[],[f66,f118])).
% 1.47/0.55  fof(f66,plain,(
% 1.47/0.55    l1_pre_topc(sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f51])).
% 1.47/0.55  fof(f116,plain,(
% 1.47/0.55    spl4_3),
% 1.47/0.55    inference(avatar_split_clause,[],[f65,f113])).
% 1.47/0.55  fof(f65,plain,(
% 1.47/0.55    v2_tdlat_3(sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f51])).
% 1.47/0.55  fof(f111,plain,(
% 1.47/0.55    spl4_2),
% 1.47/0.55    inference(avatar_split_clause,[],[f64,f108])).
% 1.47/0.55  fof(f64,plain,(
% 1.47/0.55    v2_pre_topc(sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f51])).
% 1.47/0.55  fof(f106,plain,(
% 1.47/0.55    ~spl4_1),
% 1.47/0.55    inference(avatar_split_clause,[],[f63,f103])).
% 1.47/0.55  fof(f63,plain,(
% 1.47/0.55    ~v2_struct_0(sK0)),
% 1.47/0.55    inference(cnf_transformation,[],[f51])).
% 1.47/0.55  % SZS output end Proof for theBenchmark
% 1.47/0.55  % (16913)------------------------------
% 1.47/0.55  % (16913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (16913)Termination reason: Refutation
% 1.47/0.55  
% 1.47/0.55  % (16913)Memory used [KB]: 11129
% 1.47/0.55  % (16913)Time elapsed: 0.114 s
% 1.47/0.55  % (16913)------------------------------
% 1.47/0.55  % (16913)------------------------------
% 1.47/0.55  % (16889)Success in time 0.197 s
%------------------------------------------------------------------------------
