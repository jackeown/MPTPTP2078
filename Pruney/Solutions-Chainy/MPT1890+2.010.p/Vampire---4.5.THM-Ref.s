%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:13 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 252 expanded)
%              Number of leaves         :   36 ( 112 expanded)
%              Depth                    :   10
%              Number of atoms          :  563 (1203 expanded)
%              Number of equality atoms :   40 ( 110 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f405,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f127,f156,f162,f172,f181,f197,f203,f253,f294,f299,f335,f363,f377,f388,f404])).

fof(f404,plain,
    ( spl5_7
    | ~ spl5_12
    | ~ spl5_31
    | spl5_29 ),
    inference(avatar_split_clause,[],[f395,f371,f379,f167,f115])).

fof(f115,plain,
    ( spl5_7
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f167,plain,
    ( spl5_12
  <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f379,plain,
    ( spl5_31
  <=> m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f371,plain,
    ( spl5_29
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f395,plain,
    ( ~ m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl5_29 ),
    inference(superposition,[],[f372,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f372,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f371])).

fof(f388,plain,
    ( ~ spl5_18
    | spl5_31 ),
    inference(avatar_split_clause,[],[f385,f379,f201])).

fof(f201,plain,
    ( spl5_18
  <=> r1_tarski(k1_tarski(sK2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f385,plain,
    ( ~ r1_tarski(k1_tarski(sK2(sK0,sK1)),u1_struct_0(sK0))
    | spl5_31 ),
    inference(resolution,[],[f380,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f380,plain,
    ( ~ m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_31 ),
    inference(avatar_component_clause,[],[f379])).

fof(f377,plain,
    ( ~ spl5_29
    | ~ spl5_13
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f368,f361,f170,f371])).

fof(f170,plain,
    ( spl5_13
  <=> k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f361,plain,
    ( spl5_28
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f368,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_13
    | ~ spl5_28 ),
    inference(trivial_inequality_removal,[],[f365])).

fof(f365,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_13
    | ~ spl5_28 ),
    inference(superposition,[],[f362,f171])).

fof(f171,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f170])).

fof(f362,plain,
    ( ! [X0] :
        ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f361])).

fof(f363,plain,
    ( ~ spl5_3
    | spl5_28
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f359,f333,f361,f78])).

fof(f78,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f333,plain,
    ( spl5_27
  <=> ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f359,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_27 ),
    inference(duplicate_literal_removal,[],[f356])).

fof(f356,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_27 ),
    inference(resolution,[],[f334,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f334,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f333])).

fof(f335,plain,
    ( ~ spl5_5
    | ~ spl5_3
    | spl5_27
    | ~ spl5_9
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f331,f297,f125,f333,f78,f86])).

fof(f86,plain,
    ( spl5_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f125,plain,
    ( spl5_9
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f297,plain,
    ( spl5_26
  <=> ! [X0] :
        ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,X0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f331,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_9
    | ~ spl5_26 ),
    inference(resolution,[],[f327,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f327,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,X0) )
    | ~ spl5_9
    | ~ spl5_26 ),
    inference(duplicate_literal_removal,[],[f326])).

fof(f326,plain,
    ( ! [X0] :
        ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_9
    | ~ spl5_26 ),
    inference(resolution,[],[f298,f126])).

fof(f126,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f297])).

fof(f299,plain,
    ( ~ spl5_2
    | spl5_26
    | spl5_1
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f295,f251,f70,f297,f74])).

fof(f74,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f70,plain,
    ( spl5_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f251,plain,
    ( spl5_23
  <=> ! [X1,X0] :
        ( k9_subset_1(u1_struct_0(sK0),X0,X1) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0))
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f295,plain,
    ( ! [X0] :
        ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0) )
    | spl5_1
    | ~ spl5_23 ),
    inference(resolution,[],[f252,f71])).

fof(f71,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X0,sK0)
        | k9_subset_1(u1_struct_0(sK0),X0,X1) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f251])).

fof(f294,plain,
    ( ~ spl5_2
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_7
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f161,f280])).

fof(f280,plain,
    ( ! [X6] : ~ r2_hidden(X6,sK1)
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f276,f75])).

fof(f75,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f116,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f116,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f161,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl5_11
  <=> r2_hidden(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f253,plain,
    ( ~ spl5_5
    | ~ spl5_3
    | spl5_23
    | spl5_6 ),
    inference(avatar_split_clause,[],[f249,f90,f251,f78,f86])).

fof(f90,plain,
    ( spl5_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( k9_subset_1(u1_struct_0(sK0),X0,X1) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0))
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_tex_2(X0,sK0) )
    | spl5_6 ),
    inference(resolution,[],[f52,f91])).

fof(f91,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( v2_struct_0(X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1))
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ? [X2] :
              ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2)
                            & v3_pre_topc(X3,X0) ) )
                    & r2_hidden(X2,X1) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).

fof(f203,plain,
    ( spl5_18
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f199,f179,f201])).

fof(f179,plain,
    ( spl5_15
  <=> r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f199,plain,
    ( r1_tarski(k1_tarski(sK2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl5_15 ),
    inference(resolution,[],[f196,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f196,plain,
    ( r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f179])).

fof(f197,plain,
    ( spl5_15
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f193,f160,f74,f179])).

fof(f193,plain,
    ( r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_11 ),
    inference(resolution,[],[f192,f75])).

fof(f192,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
        | r2_hidden(sK2(sK0,sK1),X1) )
    | ~ spl5_11 ),
    inference(resolution,[],[f164,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r2_hidden(sK2(sK0,sK1),X0) )
    | ~ spl5_11 ),
    inference(resolution,[],[f161,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f181,plain,
    ( ~ spl5_15
    | spl5_12 ),
    inference(avatar_split_clause,[],[f177,f167,f179])).

fof(f177,plain,
    ( ~ r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0))
    | spl5_12 ),
    inference(resolution,[],[f168,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f168,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f167])).

fof(f172,plain,
    ( ~ spl5_12
    | spl5_13
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f163,f160,f170,f167])).

fof(f163,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))
    | ~ m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | ~ spl5_11 ),
    inference(resolution,[],[f161,f48])).

fof(f48,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK1)
      | k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & ! [X2] :
        ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & ! [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & ! [X2] :
            ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            | ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(sK1,sK0)
      & ! [X2] :
          ( k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          | ~ r2_hidden(X2,sK1)
          | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & ! [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
             => v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) )
           => v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).

fof(f162,plain,
    ( ~ spl5_2
    | spl5_11
    | spl5_1
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f157,f154,f70,f160,f74])).

fof(f154,plain,
    ( spl5_10
  <=> ! [X0] :
        ( r2_hidden(sK2(sK0,X0),X0)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f157,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_10 ),
    inference(resolution,[],[f155,f71])).

fof(f155,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | r2_hidden(sK2(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f156,plain,
    ( ~ spl5_5
    | ~ spl5_3
    | spl5_10
    | spl5_6 ),
    inference(avatar_split_clause,[],[f151,f90,f154,f78,f86])).

fof(f151,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_tex_2(X0,sK0) )
    | spl5_6 ),
    inference(resolution,[],[f51,f91])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f127,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_9
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f121,f86,f125,f82,f78])).

fof(f82,plain,
    ( spl5_4
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(X0,sK0) )
    | ~ spl5_5 ),
    inference(resolution,[],[f53,f87])).

fof(f87,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK3(X0),X0)
            & v4_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f92,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f44,f86])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f45,f82])).

fof(f45,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f46,f78])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f47,f74])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f49,f70])).

fof(f49,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:12:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (30500)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.49  % (30508)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (30508)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f405,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f72,f76,f80,f84,f88,f92,f127,f156,f162,f172,f181,f197,f203,f253,f294,f299,f335,f363,f377,f388,f404])).
% 0.22/0.53  fof(f404,plain,(
% 0.22/0.53    spl5_7 | ~spl5_12 | ~spl5_31 | spl5_29),
% 0.22/0.53    inference(avatar_split_clause,[],[f395,f371,f379,f167,f115])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    spl5_7 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    spl5_12 <=> m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.53  fof(f379,plain,(
% 0.22/0.53    spl5_31 <=> m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.22/0.53  fof(f371,plain,(
% 0.22/0.53    spl5_29 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.22/0.53  fof(f395,plain,(
% 0.22/0.53    ~m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl5_29),
% 0.22/0.53    inference(superposition,[],[f372,f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_29),
% 0.22/0.53    inference(avatar_component_clause,[],[f371])).
% 0.22/0.53  fof(f388,plain,(
% 0.22/0.53    ~spl5_18 | spl5_31),
% 0.22/0.53    inference(avatar_split_clause,[],[f385,f379,f201])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    spl5_18 <=> r1_tarski(k1_tarski(sK2(sK0,sK1)),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.53  fof(f385,plain,(
% 0.22/0.53    ~r1_tarski(k1_tarski(sK2(sK0,sK1)),u1_struct_0(sK0)) | spl5_31),
% 0.22/0.53    inference(resolution,[],[f380,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f380,plain,(
% 0.22/0.53    ~m1_subset_1(k1_tarski(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_31),
% 0.22/0.53    inference(avatar_component_clause,[],[f379])).
% 0.22/0.53  fof(f377,plain,(
% 0.22/0.53    ~spl5_29 | ~spl5_13 | ~spl5_28),
% 0.22/0.53    inference(avatar_split_clause,[],[f368,f361,f170,f371])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    spl5_13 <=> k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.53  fof(f361,plain,(
% 0.22/0.53    spl5_28 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.22/0.53  fof(f368,plain,(
% 0.22/0.53    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_13 | ~spl5_28)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f365])).
% 0.22/0.53  fof(f365,plain,(
% 0.22/0.53    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_13 | ~spl5_28)),
% 0.22/0.53    inference(superposition,[],[f362,f171])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) | ~spl5_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f170])).
% 0.22/0.53  fof(f362,plain,(
% 0.22/0.53    ( ! [X0] : (k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_28),
% 0.22/0.53    inference(avatar_component_clause,[],[f361])).
% 0.22/0.53  fof(f363,plain,(
% 0.22/0.53    ~spl5_3 | spl5_28 | ~spl5_27),
% 0.22/0.53    inference(avatar_split_clause,[],[f359,f333,f361,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    spl5_3 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    spl5_27 <=> ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.53  fof(f359,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) | ~l1_pre_topc(sK0)) ) | ~spl5_27),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f356])).
% 0.22/0.53  fof(f356,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl5_27),
% 0.22/0.53    inference(resolution,[],[f334,f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0))) ) | ~spl5_27),
% 0.22/0.53    inference(avatar_component_clause,[],[f333])).
% 0.22/0.53  fof(f335,plain,(
% 0.22/0.53    ~spl5_5 | ~spl5_3 | spl5_27 | ~spl5_9 | ~spl5_26),
% 0.22/0.53    inference(avatar_split_clause,[],[f331,f297,f125,f333,f78,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl5_5 <=> v2_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    spl5_9 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.53  fof(f297,plain,(
% 0.22/0.53    spl5_26 <=> ! [X0] : (k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,X0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.53  fof(f331,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | (~spl5_9 | ~spl5_26)),
% 0.22/0.53    inference(resolution,[],[f327,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.53  fof(f327,plain,(
% 0.22/0.53    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | (~spl5_9 | ~spl5_26)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f326])).
% 0.22/0.53  fof(f326,plain,(
% 0.22/0.53    ( ! [X0] : (k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_9 | ~spl5_26)),
% 0.22/0.53    inference(resolution,[],[f298,f126])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f125])).
% 0.22/0.53  fof(f298,plain,(
% 0.22/0.53    ( ! [X0] : (~v3_pre_topc(X0,sK0) | k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_26),
% 0.22/0.53    inference(avatar_component_clause,[],[f297])).
% 0.22/0.53  fof(f299,plain,(
% 0.22/0.53    ~spl5_2 | spl5_26 | spl5_1 | ~spl5_23),
% 0.22/0.53    inference(avatar_split_clause,[],[f295,f251,f70,f297,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl5_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    spl5_1 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    spl5_23 <=> ! [X1,X0] : (k9_subset_1(u1_struct_0(sK0),X0,X1) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0)) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.53  fof(f295,plain,(
% 0.22/0.53    ( ! [X0] : (k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) != k9_subset_1(u1_struct_0(sK0),sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) ) | (spl5_1 | ~spl5_23)),
% 0.22/0.53    inference(resolution,[],[f252,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ~v2_tex_2(sK1,sK0) | spl5_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f70])).
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_tex_2(X0,sK0) | k9_subset_1(u1_struct_0(sK0),X0,X1) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) ) | ~spl5_23),
% 0.22/0.53    inference(avatar_component_clause,[],[f251])).
% 0.22/0.53  fof(f294,plain,(
% 0.22/0.53    ~spl5_2 | ~spl5_7 | ~spl5_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f286])).
% 0.22/0.53  fof(f286,plain,(
% 0.22/0.53    $false | (~spl5_2 | ~spl5_7 | ~spl5_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f161,f280])).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    ( ! [X6] : (~r2_hidden(X6,sK1)) ) | (~spl5_2 | ~spl5_7)),
% 0.22/0.53    inference(resolution,[],[f276,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f74])).
% 0.22/0.53  fof(f276,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,X0)) ) | ~spl5_7),
% 0.22/0.53    inference(resolution,[],[f116,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f115])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    r2_hidden(sK2(sK0,sK1),sK1) | ~spl5_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f160])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    spl5_11 <=> r2_hidden(sK2(sK0,sK1),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.53  fof(f253,plain,(
% 0.22/0.53    ~spl5_5 | ~spl5_3 | spl5_23 | spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f249,f90,f251,f78,f86])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    spl5_6 <=> v2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(sK0),X0,X1) != k6_domain_1(u1_struct_0(sK0),sK2(sK0,X0)) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_tex_2(X0,sK0)) ) | spl5_6),
% 0.22/0.53    inference(resolution,[],[f52,f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ~v2_struct_0(sK0) | spl5_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f90])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (v2_struct_0(X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),sK2(X0,X1)) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) | ? [X2] : ((! [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) != k6_domain_1(u1_struct_0(X0),X2) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = k6_domain_1(u1_struct_0(X0),X2) & v3_pre_topc(X3,X0))) & r2_hidden(X2,X1))) => v2_tex_2(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_tex_2)).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    spl5_18 | ~spl5_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f199,f179,f201])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    spl5_15 <=> r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    r1_tarski(k1_tarski(sK2(sK0,sK1)),u1_struct_0(sK0)) | ~spl5_15),
% 0.22/0.53    inference(resolution,[],[f196,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.53  fof(f196,plain,(
% 0.22/0.53    r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl5_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f179])).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    spl5_15 | ~spl5_2 | ~spl5_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f193,f160,f74,f179])).
% 0.22/0.53  fof(f193,plain,(
% 0.22/0.53    r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0)) | (~spl5_2 | ~spl5_11)),
% 0.22/0.53    inference(resolution,[],[f192,f75])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(X1)) | r2_hidden(sK2(sK0,sK1),X1)) ) | ~spl5_11),
% 0.22/0.53    inference(resolution,[],[f164,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK2(sK0,sK1),X0)) ) | ~spl5_11),
% 0.22/0.53    inference(resolution,[],[f161,f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    ~spl5_15 | spl5_12),
% 0.22/0.53    inference(avatar_split_clause,[],[f177,f167,f179])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    ~r2_hidden(sK2(sK0,sK1),u1_struct_0(sK0)) | spl5_12),
% 0.22/0.53    inference(resolution,[],[f168,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ~m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | spl5_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f167])).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    ~spl5_12 | spl5_13 | ~spl5_11),
% 0.22/0.53    inference(avatar_split_clause,[],[f163,f160,f170,f167])).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2(sK0,sK1)))) | ~m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0)) | ~spl5_11),
% 0.22/0.53    inference(resolution,[],[f161,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X2] : (~r2_hidden(X2,sK1) | k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    (~v2_tex_2(sK1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f29,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ? [X1] : (~v2_tex_2(X1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(sK1,sK0) & ! [X2] : (k6_domain_1(u1_struct_0(sK0),X2) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & ! [X2] : (k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~v2_tex_2(X1,X0) & ! [X2] : ((k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f11])).
% 0.22/0.53  fof(f11,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))) => v2_tex_2(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_tex_2)).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    ~spl5_2 | spl5_11 | spl5_1 | ~spl5_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f157,f154,f70,f160,f74])).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    spl5_10 <=> ! [X0] : (r2_hidden(sK2(sK0,X0),X0) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    r2_hidden(sK2(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_10)),
% 0.22/0.53    inference(resolution,[],[f155,f71])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    ( ! [X0] : (v2_tex_2(X0,sK0) | r2_hidden(sK2(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f154])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    ~spl5_5 | ~spl5_3 | spl5_10 | spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f151,f90,f154,f78,f86])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK2(sK0,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_tex_2(X0,sK0)) ) | spl5_6),
% 0.22/0.53    inference(resolution,[],[f51,f91])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v2_struct_0(X0) | r2_hidden(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_tex_2(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f32])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ~spl5_3 | ~spl5_4 | spl5_9 | ~spl5_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f121,f86,f125,f82,f78])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    spl5_4 <=> v3_tdlat_3(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v3_pre_topc(X0,sK0)) ) | ~spl5_5),
% 0.22/0.53    inference(resolution,[],[f53,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    v2_pre_topc(sK0) | ~spl5_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f86])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2,X0] : (~v2_pre_topc(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v3_pre_topc(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.53    inference(rectify,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    ~spl5_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f43,f90])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    spl5_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f44,f86])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    v2_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f45,f82])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    v3_tdlat_3(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    spl5_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f46,f78])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    l1_pre_topc(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f47,f74])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ~spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f49,f70])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ~v2_tex_2(sK1,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (30508)------------------------------
% 0.22/0.54  % (30508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30508)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (30508)Memory used [KB]: 11001
% 0.22/0.54  % (30508)Time elapsed: 0.099 s
% 0.22/0.54  % (30508)------------------------------
% 0.22/0.54  % (30508)------------------------------
% 0.22/0.54  % (30488)Success in time 0.168 s
%------------------------------------------------------------------------------
