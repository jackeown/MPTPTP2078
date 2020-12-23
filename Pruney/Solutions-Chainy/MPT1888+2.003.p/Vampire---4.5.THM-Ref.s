%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 337 expanded)
%              Number of leaves         :   43 ( 163 expanded)
%              Depth                    :    9
%              Number of atoms          :  602 (1360 expanded)
%              Number of equality atoms :   42 ( 155 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f108,f113,f119,f125,f132,f137,f144,f149,f155,f161,f179,f185,f191,f202,f219,f228,f240,f246,f284,f329,f347,f397])).

fof(f397,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_16
    | ~ spl4_12
    | ~ spl4_28
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f396,f343,f238,f134,f158,f90,f85])).

fof(f85,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f90,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f158,plain,
    ( spl4_16
  <=> k2_pre_topc(sK0,k1_tarski(sK2)) = k2_pre_topc(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f134,plain,
    ( spl4_12
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f238,plain,
    ( spl4_28
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,k1_tarski(X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f343,plain,
    ( spl4_42
  <=> r2_hidden(sK2,k2_pre_topc(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f396,plain,
    ( k2_pre_topc(sK0,k1_tarski(sK2)) = k2_pre_topc(sK0,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_12
    | ~ spl4_28
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f393,f136])).

fof(f136,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f393,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k1_tarski(sK1))
    | ~ spl4_28
    | ~ spl4_42 ),
    inference(resolution,[],[f345,f239])).

fof(f239,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,k1_tarski(X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k1_tarski(X0)) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f238])).

fof(f345,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k1_tarski(sK1)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f343])).

fof(f347,plain,
    ( spl4_42
    | spl4_40 ),
    inference(avatar_split_clause,[],[f340,f325,f343])).

fof(f325,plain,
    ( spl4_40
  <=> r1_xboole_0(k1_tarski(sK2),k2_pre_topc(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f340,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k1_tarski(sK1)))
    | spl4_40 ),
    inference(resolution,[],[f327,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f327,plain,
    ( ~ r1_xboole_0(k1_tarski(sK2),k2_pre_topc(sK0,k1_tarski(sK1)))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f325])).

fof(f329,plain,
    ( ~ spl4_40
    | spl4_34 ),
    inference(avatar_split_clause,[],[f323,f281,f325])).

fof(f281,plain,
    ( spl4_34
  <=> r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f323,plain,
    ( ~ r1_xboole_0(k1_tarski(sK2),k2_pre_topc(sK0,k1_tarski(sK1)))
    | spl4_34 ),
    inference(resolution,[],[f283,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f283,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2))
    | spl4_34 ),
    inference(avatar_component_clause,[],[f281])).

fof(f284,plain,
    ( ~ spl4_34
    | spl4_15
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f263,f244,f188,f182,f176,f152,f281])).

fof(f152,plain,
    ( spl4_15
  <=> r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f176,plain,
    ( spl4_18
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f182,plain,
    ( spl4_19
  <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f188,plain,
    ( spl4_20
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f244,plain,
    ( spl4_29
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(k2_pre_topc(sK0,X0),X1)
        | r1_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f263,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2))
    | spl4_15
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_29 ),
    inference(unit_resulting_resolution,[],[f178,f184,f154,f190,f245])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(k2_pre_topc(sK0,X0),X1)
        | r1_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f244])).

fof(f190,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f188])).

fof(f154,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2)))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f152])).

fof(f184,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f178,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f176])).

fof(f246,plain,
    ( ~ spl4_7
    | ~ spl4_5
    | spl4_29
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f242,f226,f244,f95,f105])).

fof(f105,plain,
    ( spl4_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f95,plain,
    ( spl4_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f226,plain,
    ( spl4_26
  <=> ! [X0] :
        ( v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f242,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))
        | ~ r1_xboole_0(k2_pre_topc(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_26 ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))
        | ~ r1_xboole_0(k2_pre_topc(sK0,X0),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_26 ),
    inference(resolution,[],[f227,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X1,k2_pre_topc(X0,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ r1_xboole_0(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X1,X0)
                  & r1_xboole_0(X1,X2) )
               => r1_xboole_0(X1,k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).

fof(f227,plain,
    ( ! [X0] :
        ( v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f226])).

fof(f240,plain,
    ( spl4_10
    | spl4_28
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f236,f217,f238,f122])).

fof(f122,plain,
    ( spl4_10
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f217,plain,
    ( spl4_25
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,k1_tarski(X0)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k1_tarski(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl4_25 ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,k1_tarski(X0)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k1_tarski(X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl4_25 ),
    inference(superposition,[],[f218,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f217])).

fof(f228,plain,
    ( ~ spl4_7
    | ~ spl4_5
    | spl4_26
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f224,f200,f226,f95,f105])).

fof(f200,plain,
    ( spl4_22
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f224,plain,
    ( ! [X0] :
        ( v3_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl4_22 ),
    inference(resolution,[],[f201,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f201,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f200])).

fof(f219,plain,
    ( spl4_8
    | ~ spl4_6
    | ~ spl4_5
    | spl4_25
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f215,f105,f217,f95,f100,f110])).

fof(f110,plain,
    ( spl4_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f100,plain,
    ( spl4_6
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v3_tdlat_3(sK0)
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | v2_struct_0(sK0) )
    | ~ spl4_7 ),
    inference(resolution,[],[f60,f107])).

fof(f107,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).

fof(f202,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_22
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f198,f105,f200,f100,f95])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tdlat_3(sK0)
        | ~ l1_pre_topc(sK0)
        | v3_pre_topc(X0,sK0) )
    | ~ spl4_7 ),
    inference(resolution,[],[f67,f107])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK3(X0),X0)
        & v4_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f191,plain,
    ( spl4_20
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f186,f176,f95,f188])).

fof(f186,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f97,f178,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f97,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f185,plain,
    ( spl4_19
    | ~ spl4_3
    | spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f180,f134,f122,f85,f182])).

fof(f180,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f170,f136])).

fof(f170,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f124,f87,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f87,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f124,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f179,plain,
    ( spl4_18
    | ~ spl4_4
    | spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f174,f129,f122,f90,f176])).

fof(f129,plain,
    ( spl4_11
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f174,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | spl4_10
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f171,f131])).

fof(f131,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f171,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f124,f92,f66])).

fof(f92,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f161,plain,
    ( ~ spl4_16
    | ~ spl4_11
    | spl4_13 ),
    inference(avatar_split_clause,[],[f156,f141,f129,f158])).

fof(f141,plain,
    ( spl4_13
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f156,plain,
    ( k2_pre_topc(sK0,k1_tarski(sK2)) != k2_pre_topc(sK0,k1_tarski(sK1))
    | ~ spl4_11
    | spl4_13 ),
    inference(forward_demodulation,[],[f143,f131])).

fof(f143,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k1_tarski(sK2))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f155,plain,
    ( ~ spl4_15
    | ~ spl4_11
    | spl4_14 ),
    inference(avatar_split_clause,[],[f150,f146,f129,f152])).

fof(f146,plain,
    ( spl4_14
  <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f150,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2)))
    | ~ spl4_11
    | spl4_14 ),
    inference(forward_demodulation,[],[f148,f131])).

fof(f148,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k1_tarski(sK2)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f146])).

fof(f149,plain,
    ( ~ spl4_14
    | spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f139,f134,f80,f146])).

fof(f80,plain,
    ( spl4_2
  <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f139,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k1_tarski(sK2)))
    | spl4_2
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f82,f136])).

fof(f82,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f144,plain,
    ( ~ spl4_13
    | spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f138,f134,f75,f141])).

fof(f75,plain,
    ( spl4_1
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f138,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k1_tarski(sK2))
    | spl4_1
    | ~ spl4_12 ),
    inference(backward_demodulation,[],[f77,f136])).

fof(f77,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f137,plain,
    ( spl4_12
    | ~ spl4_3
    | spl4_10 ),
    inference(avatar_split_clause,[],[f126,f122,f85,f134])).

fof(f126,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ spl4_3
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f87,f124,f58])).

fof(f132,plain,
    ( spl4_11
    | ~ spl4_4
    | spl4_10 ),
    inference(avatar_split_clause,[],[f127,f122,f90,f129])).

fof(f127,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl4_4
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f92,f124,f58])).

fof(f125,plain,
    ( ~ spl4_10
    | spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f120,f116,f110,f122])).

fof(f116,plain,
    ( spl4_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f120,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl4_8
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f112,f118,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f118,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f112,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f110])).

fof(f119,plain,
    ( spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f114,f95,f116])).

fof(f114,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f97,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f113,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f50,f110])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
              & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
            & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
          & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
      & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).

fof(f108,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f51,f105])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f52,f100])).

fof(f52,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f53,f95])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f54,f90])).

fof(f54,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f55,f85])).

fof(f55,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f56,f80])).

fof(f56,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f57,f75])).

fof(f57,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:48:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (21441)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (21440)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (21456)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  % (21443)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (21444)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (21439)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (21451)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (21452)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.52  % (21449)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (21443)Refutation not found, incomplete strategy% (21443)------------------------------
% 0.22/0.52  % (21443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21447)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (21445)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (21455)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (21453)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (21442)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (21450)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (21437)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (21445)Refutation not found, incomplete strategy% (21445)------------------------------
% 0.22/0.52  % (21445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21451)Refutation not found, incomplete strategy% (21451)------------------------------
% 0.22/0.52  % (21451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21443)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21443)Memory used [KB]: 10490
% 0.22/0.52  % (21443)Time elapsed: 0.085 s
% 0.22/0.52  % (21443)------------------------------
% 0.22/0.52  % (21443)------------------------------
% 0.22/0.52  % (21448)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (21441)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (21435)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (21438)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.52  % (21445)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21445)Memory used [KB]: 10618
% 0.22/0.52  % (21445)Time elapsed: 0.063 s
% 0.22/0.52  % (21445)------------------------------
% 0.22/0.52  % (21445)------------------------------
% 0.22/0.52  % (21451)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21451)Memory used [KB]: 1663
% 0.22/0.52  % (21451)Time elapsed: 0.092 s
% 0.22/0.52  % (21451)------------------------------
% 0.22/0.52  % (21451)------------------------------
% 0.22/0.52  % (21442)Refutation not found, incomplete strategy% (21442)------------------------------
% 0.22/0.52  % (21442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21442)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21442)Memory used [KB]: 6140
% 0.22/0.52  % (21442)Time elapsed: 0.102 s
% 0.22/0.52  % (21442)------------------------------
% 0.22/0.52  % (21442)------------------------------
% 0.22/0.52  % (21436)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.53  % (21457)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.53  % (21458)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.53  % (21446)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.54  % (21454)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 1.31/0.54  % (21438)Refutation not found, incomplete strategy% (21438)------------------------------
% 1.31/0.54  % (21438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (21438)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (21438)Memory used [KB]: 10618
% 1.31/0.54  % (21438)Time elapsed: 0.117 s
% 1.31/0.54  % (21438)------------------------------
% 1.31/0.54  % (21438)------------------------------
% 1.31/0.54  % SZS output start Proof for theBenchmark
% 1.31/0.54  fof(f398,plain,(
% 1.31/0.54    $false),
% 1.31/0.54    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f108,f113,f119,f125,f132,f137,f144,f149,f155,f161,f179,f185,f191,f202,f219,f228,f240,f246,f284,f329,f347,f397])).
% 1.31/0.54  fof(f397,plain,(
% 1.31/0.54    ~spl4_3 | ~spl4_4 | spl4_16 | ~spl4_12 | ~spl4_28 | ~spl4_42),
% 1.31/0.54    inference(avatar_split_clause,[],[f396,f343,f238,f134,f158,f90,f85])).
% 1.31/0.54  fof(f85,plain,(
% 1.31/0.54    spl4_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.31/0.54  fof(f90,plain,(
% 1.31/0.54    spl4_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.31/0.54  fof(f158,plain,(
% 1.31/0.54    spl4_16 <=> k2_pre_topc(sK0,k1_tarski(sK2)) = k2_pre_topc(sK0,k1_tarski(sK1))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.31/0.54  fof(f134,plain,(
% 1.31/0.54    spl4_12 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.31/0.54  fof(f238,plain,(
% 1.31/0.54    spl4_28 <=> ! [X1,X0] : (~r2_hidden(X1,k2_pre_topc(sK0,k1_tarski(X0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k1_tarski(X0)))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.31/0.54  fof(f343,plain,(
% 1.31/0.54    spl4_42 <=> r2_hidden(sK2,k2_pre_topc(sK0,k1_tarski(sK1)))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.31/0.54  fof(f396,plain,(
% 1.31/0.54    k2_pre_topc(sK0,k1_tarski(sK2)) = k2_pre_topc(sK0,k1_tarski(sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (~spl4_12 | ~spl4_28 | ~spl4_42)),
% 1.31/0.54    inference(forward_demodulation,[],[f393,f136])).
% 1.31/0.54  fof(f136,plain,(
% 1.31/0.54    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | ~spl4_12),
% 1.31/0.54    inference(avatar_component_clause,[],[f134])).
% 1.31/0.54  fof(f393,plain,(
% 1.31/0.54    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k1_tarski(sK1)) | (~spl4_28 | ~spl4_42)),
% 1.31/0.54    inference(resolution,[],[f345,f239])).
% 1.31/0.54  fof(f239,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k2_pre_topc(sK0,k1_tarski(X0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k1_tarski(X0))) ) | ~spl4_28),
% 1.31/0.54    inference(avatar_component_clause,[],[f238])).
% 1.31/0.54  fof(f345,plain,(
% 1.31/0.54    r2_hidden(sK2,k2_pre_topc(sK0,k1_tarski(sK1))) | ~spl4_42),
% 1.31/0.54    inference(avatar_component_clause,[],[f343])).
% 1.31/0.54  fof(f347,plain,(
% 1.31/0.54    spl4_42 | spl4_40),
% 1.31/0.54    inference(avatar_split_clause,[],[f340,f325,f343])).
% 1.31/0.54  fof(f325,plain,(
% 1.31/0.54    spl4_40 <=> r1_xboole_0(k1_tarski(sK2),k2_pre_topc(sK0,k1_tarski(sK1)))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.31/0.54  fof(f340,plain,(
% 1.31/0.54    r2_hidden(sK2,k2_pre_topc(sK0,k1_tarski(sK1))) | spl4_40),
% 1.31/0.54    inference(resolution,[],[f327,f62])).
% 1.31/0.54  fof(f62,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f27])).
% 1.31/0.54  fof(f27,plain,(
% 1.31/0.54    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f4])).
% 1.31/0.54  fof(f4,axiom,(
% 1.31/0.54    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).
% 1.31/0.54  fof(f327,plain,(
% 1.31/0.54    ~r1_xboole_0(k1_tarski(sK2),k2_pre_topc(sK0,k1_tarski(sK1))) | spl4_40),
% 1.31/0.54    inference(avatar_component_clause,[],[f325])).
% 1.31/0.54  fof(f329,plain,(
% 1.31/0.54    ~spl4_40 | spl4_34),
% 1.31/0.54    inference(avatar_split_clause,[],[f323,f281,f325])).
% 1.31/0.54  fof(f281,plain,(
% 1.31/0.54    spl4_34 <=> r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.31/0.54  fof(f323,plain,(
% 1.31/0.54    ~r1_xboole_0(k1_tarski(sK2),k2_pre_topc(sK0,k1_tarski(sK1))) | spl4_34),
% 1.31/0.54    inference(resolution,[],[f283,f61])).
% 1.31/0.54  fof(f61,plain,(
% 1.31/0.54    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f26])).
% 1.31/0.54  fof(f26,plain,(
% 1.31/0.54    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.31/0.54    inference(ennf_transformation,[],[f2])).
% 1.31/0.54  fof(f2,axiom,(
% 1.31/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.31/0.54  fof(f283,plain,(
% 1.31/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2)) | spl4_34),
% 1.31/0.54    inference(avatar_component_clause,[],[f281])).
% 1.31/0.54  fof(f284,plain,(
% 1.31/0.54    ~spl4_34 | spl4_15 | ~spl4_18 | ~spl4_19 | ~spl4_20 | ~spl4_29),
% 1.31/0.54    inference(avatar_split_clause,[],[f263,f244,f188,f182,f176,f152,f281])).
% 1.31/0.54  fof(f152,plain,(
% 1.31/0.54    spl4_15 <=> r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2)))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.31/0.54  fof(f176,plain,(
% 1.31/0.54    spl4_18 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.31/0.54  fof(f182,plain,(
% 1.31/0.54    spl4_19 <=> m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.31/0.54  fof(f188,plain,(
% 1.31/0.54    spl4_20 <=> m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.31/0.54  fof(f244,plain,(
% 1.31/0.54    spl4_29 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(k2_pre_topc(sK0,X0),X1) | r1_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) | ~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.31/0.54  fof(f263,plain,(
% 1.31/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k1_tarski(sK2)) | (spl4_15 | ~spl4_18 | ~spl4_19 | ~spl4_20 | ~spl4_29)),
% 1.31/0.54    inference(unit_resulting_resolution,[],[f178,f184,f154,f190,f245])).
% 1.31/0.54  fof(f245,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_xboole_0(k2_pre_topc(sK0,X0),X1) | r1_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_29),
% 1.31/0.54    inference(avatar_component_clause,[],[f244])).
% 1.31/0.54  fof(f190,plain,(
% 1.31/0.54    m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_20),
% 1.31/0.54    inference(avatar_component_clause,[],[f188])).
% 1.31/0.54  fof(f154,plain,(
% 1.31/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) | spl4_15),
% 1.31/0.54    inference(avatar_component_clause,[],[f152])).
% 1.31/0.54  fof(f184,plain,(
% 1.31/0.54    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_19),
% 1.31/0.54    inference(avatar_component_clause,[],[f182])).
% 1.31/0.54  fof(f178,plain,(
% 1.31/0.54    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_18),
% 1.31/0.54    inference(avatar_component_clause,[],[f176])).
% 1.31/0.54  fof(f246,plain,(
% 1.31/0.54    ~spl4_7 | ~spl4_5 | spl4_29 | ~spl4_26),
% 1.31/0.54    inference(avatar_split_clause,[],[f242,f226,f244,f95,f105])).
% 1.31/0.54  fof(f105,plain,(
% 1.31/0.54    spl4_7 <=> v2_pre_topc(sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.31/0.54  fof(f95,plain,(
% 1.31/0.54    spl4_5 <=> l1_pre_topc(sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.31/0.54  fof(f226,plain,(
% 1.31/0.54    spl4_26 <=> ! [X0] : (v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.31/0.54  fof(f242,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) | ~r1_xboole_0(k2_pre_topc(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_26),
% 1.31/0.54    inference(duplicate_literal_removal,[],[f241])).
% 1.31/0.54  fof(f241,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) | ~r1_xboole_0(k2_pre_topc(sK0,X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_26),
% 1.31/0.54    inference(resolution,[],[f227,f63])).
% 1.31/0.54  fof(f63,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f29])).
% 1.31/0.54  fof(f29,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.54    inference(flattening,[],[f28])).
% 1.31/0.54  fof(f28,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f14])).
% 1.31/0.54  fof(f14,axiom,(
% 1.31/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tsep_1)).
% 1.31/0.54  fof(f227,plain,(
% 1.31/0.54    ( ! [X0] : (v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_26),
% 1.31/0.54    inference(avatar_component_clause,[],[f226])).
% 1.31/0.54  fof(f240,plain,(
% 1.31/0.54    spl4_10 | spl4_28 | ~spl4_25),
% 1.31/0.54    inference(avatar_split_clause,[],[f236,f217,f238,f122])).
% 1.31/0.54  fof(f122,plain,(
% 1.31/0.54    spl4_10 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.31/0.54  fof(f217,plain,(
% 1.31/0.54    spl4_25 <=> ! [X1,X0] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.31/0.54  fof(f236,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k2_pre_topc(sK0,k1_tarski(X0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k1_tarski(X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl4_25),
% 1.31/0.54    inference(duplicate_literal_removal,[],[f235])).
% 1.31/0.54  fof(f235,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k2_pre_topc(sK0,k1_tarski(X0))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k1_tarski(X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))) ) | ~spl4_25),
% 1.31/0.54    inference(superposition,[],[f218,f58])).
% 1.31/0.54  fof(f58,plain,(
% 1.31/0.54    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f21])).
% 1.31/0.54  fof(f21,plain,(
% 1.31/0.54    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.31/0.54    inference(flattening,[],[f20])).
% 1.31/0.54  fof(f20,plain,(
% 1.31/0.54    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f11])).
% 1.31/0.54  fof(f11,axiom,(
% 1.31/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.31/0.54  fof(f218,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl4_25),
% 1.31/0.54    inference(avatar_component_clause,[],[f217])).
% 1.31/0.54  fof(f228,plain,(
% 1.31/0.54    ~spl4_7 | ~spl4_5 | spl4_26 | ~spl4_22),
% 1.31/0.54    inference(avatar_split_clause,[],[f224,f200,f226,f95,f105])).
% 1.31/0.54  fof(f200,plain,(
% 1.31/0.54    spl4_22 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.31/0.54  fof(f224,plain,(
% 1.31/0.54    ( ! [X0] : (v3_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl4_22),
% 1.31/0.54    inference(resolution,[],[f201,f65])).
% 1.31/0.54  fof(f65,plain,(
% 1.31/0.54    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f33])).
% 1.31/0.54  fof(f33,plain,(
% 1.31/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.54    inference(flattening,[],[f32])).
% 1.31/0.54  fof(f32,plain,(
% 1.31/0.54    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f12])).
% 1.31/0.54  fof(f12,axiom,(
% 1.31/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 1.31/0.54  fof(f201,plain,(
% 1.31/0.54    ( ! [X0] : (~v4_pre_topc(X0,sK0) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_22),
% 1.31/0.54    inference(avatar_component_clause,[],[f200])).
% 1.31/0.54  fof(f219,plain,(
% 1.31/0.54    spl4_8 | ~spl4_6 | ~spl4_5 | spl4_25 | ~spl4_7),
% 1.31/0.54    inference(avatar_split_clause,[],[f215,f105,f217,f95,f100,f110])).
% 1.31/0.54  fof(f110,plain,(
% 1.31/0.54    spl4_8 <=> v2_struct_0(sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.31/0.54  fof(f100,plain,(
% 1.31/0.54    spl4_6 <=> v3_tdlat_3(sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.31/0.54  fof(f215,plain,(
% 1.31/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v3_tdlat_3(sK0) | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) | v2_struct_0(sK0)) ) | ~spl4_7),
% 1.31/0.54    inference(resolution,[],[f60,f107])).
% 1.31/0.54  fof(f107,plain,(
% 1.31/0.54    v2_pre_topc(sK0) | ~spl4_7),
% 1.31/0.54    inference(avatar_component_clause,[],[f105])).
% 1.31/0.54  fof(f60,plain,(
% 1.31/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f25])).
% 1.31/0.54  fof(f25,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.31/0.54    inference(flattening,[],[f24])).
% 1.31/0.54  fof(f24,plain,(
% 1.31/0.54    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f15])).
% 1.31/0.54  fof(f15,axiom,(
% 1.31/0.54    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tex_2)).
% 1.31/0.54  fof(f202,plain,(
% 1.31/0.54    ~spl4_5 | ~spl4_6 | spl4_22 | ~spl4_7),
% 1.31/0.54    inference(avatar_split_clause,[],[f198,f105,f200,f100,f95])).
% 1.31/0.54  fof(f198,plain,(
% 1.31/0.54    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v3_pre_topc(X0,sK0)) ) | ~spl4_7),
% 1.31/0.54    inference(resolution,[],[f67,f107])).
% 1.31/0.54  fof(f67,plain,(
% 1.31/0.54    ( ! [X2,X0] : (~v2_pre_topc(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v3_pre_topc(X2,X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f49])).
% 1.31/0.54  fof(f49,plain,(
% 1.31/0.54    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 1.31/0.54  fof(f48,plain,(
% 1.31/0.54    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f47,plain,(
% 1.31/0.54    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.54    inference(rectify,[],[f46])).
% 1.31/0.54  fof(f46,plain,(
% 1.31/0.54    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.54    inference(nnf_transformation,[],[f37])).
% 1.31/0.54  fof(f37,plain,(
% 1.31/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.31/0.54    inference(flattening,[],[f36])).
% 1.31/0.54  fof(f36,plain,(
% 1.31/0.54    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f13])).
% 1.31/0.54  fof(f13,axiom,(
% 1.31/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tdlat_3)).
% 1.31/0.54  fof(f191,plain,(
% 1.31/0.54    spl4_20 | ~spl4_5 | ~spl4_18),
% 1.31/0.54    inference(avatar_split_clause,[],[f186,f176,f95,f188])).
% 1.31/0.54  fof(f186,plain,(
% 1.31/0.54    m1_subset_1(k2_pre_topc(sK0,k1_tarski(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_5 | ~spl4_18)),
% 1.31/0.54    inference(unit_resulting_resolution,[],[f97,f178,f64])).
% 1.31/0.54  fof(f64,plain,(
% 1.31/0.54    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f31])).
% 1.31/0.54  fof(f31,plain,(
% 1.31/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.31/0.54    inference(flattening,[],[f30])).
% 1.31/0.54  fof(f30,plain,(
% 1.31/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f7])).
% 1.31/0.54  fof(f7,axiom,(
% 1.31/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.31/0.54  fof(f97,plain,(
% 1.31/0.54    l1_pre_topc(sK0) | ~spl4_5),
% 1.31/0.54    inference(avatar_component_clause,[],[f95])).
% 1.31/0.54  fof(f185,plain,(
% 1.31/0.54    spl4_19 | ~spl4_3 | spl4_10 | ~spl4_12),
% 1.31/0.54    inference(avatar_split_clause,[],[f180,f134,f122,f85,f182])).
% 1.31/0.54  fof(f180,plain,(
% 1.31/0.54    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_3 | spl4_10 | ~spl4_12)),
% 1.31/0.54    inference(forward_demodulation,[],[f170,f136])).
% 1.31/0.54  fof(f170,plain,(
% 1.31/0.54    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_3 | spl4_10)),
% 1.31/0.54    inference(unit_resulting_resolution,[],[f124,f87,f66])).
% 1.31/0.54  fof(f66,plain,(
% 1.31/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f35])).
% 1.31/0.54  fof(f35,plain,(
% 1.31/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.31/0.54    inference(flattening,[],[f34])).
% 1.31/0.54  fof(f34,plain,(
% 1.31/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f10])).
% 1.31/0.54  fof(f10,axiom,(
% 1.31/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.31/0.54  fof(f87,plain,(
% 1.31/0.54    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl4_3),
% 1.31/0.54    inference(avatar_component_clause,[],[f85])).
% 1.31/0.54  fof(f124,plain,(
% 1.31/0.54    ~v1_xboole_0(u1_struct_0(sK0)) | spl4_10),
% 1.31/0.54    inference(avatar_component_clause,[],[f122])).
% 1.31/0.54  fof(f179,plain,(
% 1.31/0.54    spl4_18 | ~spl4_4 | spl4_10 | ~spl4_11),
% 1.31/0.54    inference(avatar_split_clause,[],[f174,f129,f122,f90,f176])).
% 1.31/0.54  fof(f129,plain,(
% 1.31/0.54    spl4_11 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.31/0.54  fof(f174,plain,(
% 1.31/0.54    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | spl4_10 | ~spl4_11)),
% 1.31/0.54    inference(forward_demodulation,[],[f171,f131])).
% 1.31/0.54  fof(f131,plain,(
% 1.31/0.54    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~spl4_11),
% 1.31/0.54    inference(avatar_component_clause,[],[f129])).
% 1.31/0.54  fof(f171,plain,(
% 1.31/0.54    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | spl4_10)),
% 1.31/0.54    inference(unit_resulting_resolution,[],[f124,f92,f66])).
% 1.31/0.54  fof(f92,plain,(
% 1.31/0.54    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_4),
% 1.31/0.54    inference(avatar_component_clause,[],[f90])).
% 1.31/0.54  fof(f161,plain,(
% 1.31/0.54    ~spl4_16 | ~spl4_11 | spl4_13),
% 1.31/0.54    inference(avatar_split_clause,[],[f156,f141,f129,f158])).
% 1.31/0.54  fof(f141,plain,(
% 1.31/0.54    spl4_13 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k1_tarski(sK2))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.31/0.54  fof(f156,plain,(
% 1.31/0.54    k2_pre_topc(sK0,k1_tarski(sK2)) != k2_pre_topc(sK0,k1_tarski(sK1)) | (~spl4_11 | spl4_13)),
% 1.31/0.54    inference(forward_demodulation,[],[f143,f131])).
% 1.31/0.54  fof(f143,plain,(
% 1.31/0.54    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k1_tarski(sK2)) | spl4_13),
% 1.31/0.54    inference(avatar_component_clause,[],[f141])).
% 1.31/0.54  fof(f155,plain,(
% 1.31/0.54    ~spl4_15 | ~spl4_11 | spl4_14),
% 1.31/0.54    inference(avatar_split_clause,[],[f150,f146,f129,f152])).
% 1.31/0.54  fof(f146,plain,(
% 1.31/0.54    spl4_14 <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k1_tarski(sK2)))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.31/0.54  fof(f150,plain,(
% 1.31/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k1_tarski(sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) | (~spl4_11 | spl4_14)),
% 1.31/0.54    inference(forward_demodulation,[],[f148,f131])).
% 1.31/0.54  fof(f148,plain,(
% 1.31/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) | spl4_14),
% 1.31/0.54    inference(avatar_component_clause,[],[f146])).
% 1.31/0.54  fof(f149,plain,(
% 1.31/0.54    ~spl4_14 | spl4_2 | ~spl4_12),
% 1.31/0.54    inference(avatar_split_clause,[],[f139,f134,f80,f146])).
% 1.31/0.54  fof(f80,plain,(
% 1.31/0.54    spl4_2 <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.31/0.54  fof(f139,plain,(
% 1.31/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k1_tarski(sK2))) | (spl4_2 | ~spl4_12)),
% 1.31/0.54    inference(backward_demodulation,[],[f82,f136])).
% 1.31/0.54  fof(f82,plain,(
% 1.31/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl4_2),
% 1.31/0.54    inference(avatar_component_clause,[],[f80])).
% 1.31/0.54  fof(f144,plain,(
% 1.31/0.54    ~spl4_13 | spl4_1 | ~spl4_12),
% 1.31/0.54    inference(avatar_split_clause,[],[f138,f134,f75,f141])).
% 1.31/0.54  fof(f75,plain,(
% 1.31/0.54    spl4_1 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.31/0.54  fof(f138,plain,(
% 1.31/0.54    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k1_tarski(sK2)) | (spl4_1 | ~spl4_12)),
% 1.31/0.54    inference(backward_demodulation,[],[f77,f136])).
% 1.31/0.54  fof(f77,plain,(
% 1.31/0.54    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | spl4_1),
% 1.31/0.54    inference(avatar_component_clause,[],[f75])).
% 1.31/0.54  fof(f137,plain,(
% 1.31/0.54    spl4_12 | ~spl4_3 | spl4_10),
% 1.31/0.54    inference(avatar_split_clause,[],[f126,f122,f85,f134])).
% 1.31/0.54  fof(f126,plain,(
% 1.31/0.54    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | (~spl4_3 | spl4_10)),
% 1.31/0.54    inference(unit_resulting_resolution,[],[f87,f124,f58])).
% 1.31/0.54  fof(f132,plain,(
% 1.31/0.54    spl4_11 | ~spl4_4 | spl4_10),
% 1.31/0.54    inference(avatar_split_clause,[],[f127,f122,f90,f129])).
% 1.31/0.54  fof(f127,plain,(
% 1.31/0.54    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | (~spl4_4 | spl4_10)),
% 1.31/0.54    inference(unit_resulting_resolution,[],[f92,f124,f58])).
% 1.31/0.54  fof(f125,plain,(
% 1.31/0.54    ~spl4_10 | spl4_8 | ~spl4_9),
% 1.31/0.54    inference(avatar_split_clause,[],[f120,f116,f110,f122])).
% 1.31/0.54  fof(f116,plain,(
% 1.31/0.54    spl4_9 <=> l1_struct_0(sK0)),
% 1.31/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.31/0.54  fof(f120,plain,(
% 1.31/0.54    ~v1_xboole_0(u1_struct_0(sK0)) | (spl4_8 | ~spl4_9)),
% 1.31/0.54    inference(unit_resulting_resolution,[],[f112,f118,f72])).
% 1.31/0.54  fof(f72,plain,(
% 1.31/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f40])).
% 1.31/0.54  fof(f40,plain,(
% 1.31/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.31/0.54    inference(flattening,[],[f39])).
% 1.31/0.54  fof(f39,plain,(
% 1.31/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f9])).
% 1.31/0.54  fof(f9,axiom,(
% 1.31/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.31/0.54  fof(f118,plain,(
% 1.31/0.54    l1_struct_0(sK0) | ~spl4_9),
% 1.31/0.54    inference(avatar_component_clause,[],[f116])).
% 1.31/0.54  fof(f112,plain,(
% 1.31/0.54    ~v2_struct_0(sK0) | spl4_8),
% 1.31/0.54    inference(avatar_component_clause,[],[f110])).
% 1.31/0.54  fof(f119,plain,(
% 1.31/0.54    spl4_9 | ~spl4_5),
% 1.31/0.54    inference(avatar_split_clause,[],[f114,f95,f116])).
% 1.31/0.54  fof(f114,plain,(
% 1.31/0.54    l1_struct_0(sK0) | ~spl4_5),
% 1.31/0.54    inference(unit_resulting_resolution,[],[f97,f73])).
% 1.31/0.54  fof(f73,plain,(
% 1.31/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.31/0.54    inference(cnf_transformation,[],[f41])).
% 1.31/0.54  fof(f41,plain,(
% 1.31/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.31/0.54    inference(ennf_transformation,[],[f8])).
% 1.31/0.54  fof(f8,axiom,(
% 1.31/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.31/0.54  fof(f113,plain,(
% 1.31/0.54    ~spl4_8),
% 1.31/0.54    inference(avatar_split_clause,[],[f50,f110])).
% 1.31/0.54  fof(f50,plain,(
% 1.31/0.54    ~v2_struct_0(sK0)),
% 1.31/0.54    inference(cnf_transformation,[],[f45])).
% 1.31/0.54  fof(f45,plain,(
% 1.31/0.54    ((k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.31/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f44,f43,f42])).
% 1.31/0.54  fof(f42,plain,(
% 1.31/0.54    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f43,plain,(
% 1.31/0.54    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f44,plain,(
% 1.31/0.54    ? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) => (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.31/0.54    introduced(choice_axiom,[])).
% 1.31/0.54  fof(f19,plain,(
% 1.31/0.54    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.31/0.54    inference(flattening,[],[f18])).
% 1.31/0.54  fof(f18,plain,(
% 1.31/0.54    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.31/0.54    inference(ennf_transformation,[],[f17])).
% 1.31/0.54  fof(f17,negated_conjecture,(
% 1.31/0.54    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 1.31/0.54    inference(negated_conjecture,[],[f16])).
% 1.31/0.54  fof(f16,conjecture,(
% 1.31/0.54    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 1.31/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tex_2)).
% 1.31/0.54  fof(f108,plain,(
% 1.31/0.54    spl4_7),
% 1.31/0.54    inference(avatar_split_clause,[],[f51,f105])).
% 1.31/0.54  fof(f51,plain,(
% 1.31/0.54    v2_pre_topc(sK0)),
% 1.31/0.54    inference(cnf_transformation,[],[f45])).
% 1.31/0.54  fof(f103,plain,(
% 1.31/0.54    spl4_6),
% 1.31/0.54    inference(avatar_split_clause,[],[f52,f100])).
% 1.31/0.54  fof(f52,plain,(
% 1.31/0.54    v3_tdlat_3(sK0)),
% 1.31/0.54    inference(cnf_transformation,[],[f45])).
% 1.31/0.54  fof(f98,plain,(
% 1.31/0.54    spl4_5),
% 1.31/0.54    inference(avatar_split_clause,[],[f53,f95])).
% 1.31/0.54  fof(f53,plain,(
% 1.31/0.54    l1_pre_topc(sK0)),
% 1.31/0.54    inference(cnf_transformation,[],[f45])).
% 1.31/0.54  fof(f93,plain,(
% 1.31/0.54    spl4_4),
% 1.31/0.54    inference(avatar_split_clause,[],[f54,f90])).
% 1.31/0.54  fof(f54,plain,(
% 1.31/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.31/0.54    inference(cnf_transformation,[],[f45])).
% 1.31/0.54  fof(f88,plain,(
% 1.31/0.54    spl4_3),
% 1.31/0.54    inference(avatar_split_clause,[],[f55,f85])).
% 1.31/0.54  fof(f55,plain,(
% 1.31/0.54    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.31/0.54    inference(cnf_transformation,[],[f45])).
% 1.31/0.54  fof(f83,plain,(
% 1.31/0.54    ~spl4_2),
% 1.31/0.54    inference(avatar_split_clause,[],[f56,f80])).
% 1.31/0.54  fof(f56,plain,(
% 1.31/0.54    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 1.31/0.54    inference(cnf_transformation,[],[f45])).
% 1.31/0.54  fof(f78,plain,(
% 1.31/0.54    ~spl4_1),
% 1.31/0.54    inference(avatar_split_clause,[],[f57,f75])).
% 1.31/0.54  fof(f57,plain,(
% 1.31/0.54    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 1.31/0.54    inference(cnf_transformation,[],[f45])).
% 1.31/0.54  % SZS output end Proof for theBenchmark
% 1.31/0.54  % (21441)------------------------------
% 1.31/0.54  % (21441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (21441)Termination reason: Refutation
% 1.31/0.54  
% 1.31/0.54  % (21441)Memory used [KB]: 10874
% 1.31/0.54  % (21441)Time elapsed: 0.101 s
% 1.31/0.54  % (21441)------------------------------
% 1.31/0.54  % (21441)------------------------------
% 1.31/0.54  % (21434)Success in time 0.171 s
%------------------------------------------------------------------------------
