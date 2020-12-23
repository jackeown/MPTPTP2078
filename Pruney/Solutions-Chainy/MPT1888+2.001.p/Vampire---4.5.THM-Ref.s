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
% DateTime   : Thu Dec  3 13:22:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 394 expanded)
%              Number of leaves         :   49 ( 189 expanded)
%              Depth                    :    9
%              Number of atoms          :  622 (1419 expanded)
%              Number of equality atoms :   31 ( 130 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f992,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f113,f118,f123,f201,f235,f246,f271,f285,f312,f347,f348,f349,f350,f353,f360,f411,f455,f469,f498,f546,f552,f572,f801,f987])).

fof(f987,plain,
    ( ~ spl5_62
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_37
    | spl5_53
    | ~ spl5_64
    | ~ spl5_90 ),
    inference(avatar_split_clause,[],[f985,f798,f569,f466,f357,f115,f105,f548])).

fof(f548,plain,
    ( spl5_62
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f105,plain,
    ( spl5_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f115,plain,
    ( spl5_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f357,plain,
    ( spl5_37
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f466,plain,
    ( spl5_53
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f569,plain,
    ( spl5_64
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f798,plain,
    ( spl5_90
  <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f985,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_37
    | spl5_53
    | ~ spl5_64
    | ~ spl5_90 ),
    inference(unit_resulting_resolution,[],[f117,f107,f359,f571,f468,f800,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r1_xboole_0(X1,k2_pre_topc(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).

fof(f800,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ spl5_90 ),
    inference(avatar_component_clause,[],[f798])).

fof(f468,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | spl5_53 ),
    inference(avatar_component_clause,[],[f466])).

fof(f571,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_tarski(sK1,sK1))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f569])).

fof(f359,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f357])).

fof(f107,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f117,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f801,plain,
    ( ~ spl5_62
    | spl5_90
    | ~ spl5_21
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f796,f543,f233,f798,f548])).

fof(f233,plain,
    ( spl5_21
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f543,plain,
    ( spl5_61
  <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f796,plain,
    ( v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_21
    | ~ spl5_61 ),
    inference(resolution,[],[f545,f234])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f233])).

fof(f545,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f543])).

fof(f572,plain,
    ( spl5_64
    | spl5_57 ),
    inference(avatar_split_clause,[],[f562,f495,f569])).

fof(f495,plain,
    ( spl5_57
  <=> r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f562,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_tarski(sK1,sK1))
    | spl5_57 ),
    inference(unit_resulting_resolution,[],[f497,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k2_tarski(X0,X0))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f81,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f73,f62])).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f497,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl5_57 ),
    inference(avatar_component_clause,[],[f495])).

fof(f552,plain,
    ( spl5_62
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f536,f164,f105,f548])).

fof(f164,plain,
    ( spl5_14
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f536,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f166,f190])).

fof(f190,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_5 ),
    inference(resolution,[],[f80,f107])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f166,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f546,plain,
    ( spl5_61
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f538,f164,f115,f105,f543])).

fof(f538,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f117,f107,f166,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f498,plain,
    ( ~ spl5_57
    | ~ spl5_20
    | spl5_26 ),
    inference(avatar_split_clause,[],[f493,f268,f220,f495])).

fof(f220,plain,
    ( spl5_20
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f268,plain,
    ( spl5_26
  <=> r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f493,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_20
    | spl5_26 ),
    inference(forward_demodulation,[],[f270,f222])).

fof(f222,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f220])).

fof(f270,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f268])).

fof(f469,plain,
    ( ~ spl5_53
    | spl5_51 ),
    inference(avatar_split_clause,[],[f464,f452,f466])).

fof(f452,plain,
    ( spl5_51
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f464,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))
    | spl5_51 ),
    inference(unit_resulting_resolution,[],[f454,f75])).

fof(f454,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | spl5_51 ),
    inference(avatar_component_clause,[],[f452])).

fof(f455,plain,
    ( ~ spl5_51
    | ~ spl5_20
    | spl5_45 ),
    inference(avatar_split_clause,[],[f445,f408,f220,f452])).

fof(f408,plain,
    ( spl5_45
  <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f445,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))
    | ~ spl5_20
    | spl5_45 ),
    inference(backward_demodulation,[],[f410,f222])).

fof(f410,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_45 ),
    inference(avatar_component_clause,[],[f408])).

fof(f411,plain,
    ( ~ spl5_45
    | spl5_2
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f400,f215,f90,f408])).

fof(f90,plain,
    ( spl5_2
  <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f215,plain,
    ( spl5_19
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f400,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_2
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f92,f217])).

fof(f217,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f215])).

fof(f92,plain,
    ( ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f360,plain,
    ( spl5_37
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f354,f143,f357])).

fof(f143,plain,
    ( spl5_12
  <=> r2_hidden(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f354,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f145,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f74,f62])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f145,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f353,plain,
    ( spl5_14
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f351,f134,f164])).

fof(f134,plain,
    ( spl5_10
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f351,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f136,f82])).

fof(f136,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f350,plain,
    ( spl5_20
    | ~ spl5_3
    | spl5_11 ),
    inference(avatar_split_clause,[],[f341,f138,f95,f220])).

fof(f95,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f138,plain,
    ( spl5_11
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f341,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)
    | ~ spl5_3
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f97,f139,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f78,f62])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f139,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f97,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f349,plain,
    ( spl5_19
    | ~ spl5_4
    | spl5_11 ),
    inference(avatar_split_clause,[],[f342,f138,f100,f215])).

fof(f100,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f342,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | ~ spl5_4
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f102,f139,f83])).

fof(f102,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f348,plain,
    ( spl5_10
    | ~ spl5_3
    | spl5_11 ),
    inference(avatar_split_clause,[],[f343,f138,f95,f134])).

fof(f343,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | ~ spl5_3
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f97,f139,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f347,plain,
    ( spl5_12
    | ~ spl5_4
    | spl5_11 ),
    inference(avatar_split_clause,[],[f344,f138,f100,f143])).

fof(f344,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl5_4
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f102,f139,f76])).

fof(f312,plain,
    ( spl5_28
    | ~ spl5_11
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f309,f243,f138,f282])).

fof(f282,plain,
    ( spl5_28
  <=> v1_xboole_0(k1_connsp_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f243,plain,
    ( spl5_22
  <=> m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f309,plain,
    ( v1_xboole_0(k1_connsp_2(sK0,sK1))
    | ~ spl5_11
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f140,f245,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f245,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f243])).

fof(f140,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f285,plain,
    ( ~ spl5_28
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f280,f198,f282])).

fof(f198,plain,
    ( spl5_16
  <=> r2_hidden(sK1,k1_connsp_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f280,plain,
    ( ~ v1_xboole_0(k1_connsp_2(sK0,sK1))
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f200,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f200,plain,
    ( r2_hidden(sK1,k1_connsp_2(sK0,sK1))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f198])).

fof(f271,plain,
    ( ~ spl5_26
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f259,f120,f115,f110,f105,f100,f95,f85,f268])).

fof(f85,plain,
    ( spl5_1
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f110,plain,
    ( spl5_6
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f120,plain,
    ( spl5_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f259,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f122,f117,f112,f107,f102,f97,f87,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

fof(f87,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f112,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f122,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f246,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f240,f120,f115,f105,f100,f243])).

fof(f240,plain,
    ( m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f122,f117,f107,f102,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

fof(f235,plain,
    ( ~ spl5_7
    | ~ spl5_5
    | spl5_21
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f231,f110,f233,f105,f115])).

fof(f231,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f66,f112])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ v3_tdlat_3(X0)
      | ~ v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f201,plain,
    ( spl5_16
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f196,f120,f115,f105,f100,f198])).

fof(f196,plain,
    ( r2_hidden(sK1,k1_connsp_2(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f122,f117,f107,f102,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

fof(f123,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f54,f120])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

fof(f118,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f55,f115])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f113,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f56,f110])).

fof(f56,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f108,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f57,f105])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f58,f100])).

fof(f58,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f59,f95])).

fof(f59,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f93,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f60,f90])).

fof(f60,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f61,f85])).

fof(f61,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:02:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (21821)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (21824)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (21819)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (21825)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (21822)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (21828)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (21832)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (21823)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (21829)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (21827)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (21829)Refutation not found, incomplete strategy% (21829)------------------------------
% 0.22/0.50  % (21829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21829)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (21829)Memory used [KB]: 10618
% 0.22/0.50  % (21829)Time elapsed: 0.077 s
% 0.22/0.50  % (21829)------------------------------
% 0.22/0.50  % (21829)------------------------------
% 0.22/0.50  % (21820)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (21826)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (21824)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f992,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f113,f118,f123,f201,f235,f246,f271,f285,f312,f347,f348,f349,f350,f353,f360,f411,f455,f469,f498,f546,f552,f572,f801,f987])).
% 0.22/0.51  fof(f987,plain,(
% 0.22/0.51    ~spl5_62 | ~spl5_5 | ~spl5_7 | ~spl5_37 | spl5_53 | ~spl5_64 | ~spl5_90),
% 0.22/0.51    inference(avatar_split_clause,[],[f985,f798,f569,f466,f357,f115,f105,f548])).
% 0.22/0.51  fof(f548,plain,(
% 0.22/0.51    spl5_62 <=> m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    spl5_5 <=> l1_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    spl5_7 <=> v2_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.51  fof(f357,plain,(
% 0.22/0.51    spl5_37 <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.22/0.51  fof(f466,plain,(
% 0.22/0.51    spl5_53 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 0.22/0.51  fof(f569,plain,(
% 0.22/0.51    spl5_64 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_tarski(sK1,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 0.22/0.51  fof(f798,plain,(
% 0.22/0.51    spl5_90 <=> v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).
% 0.22/0.51  fof(f985,plain,(
% 0.22/0.51    ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_5 | ~spl5_7 | ~spl5_37 | spl5_53 | ~spl5_64 | ~spl5_90)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f117,f107,f359,f571,f468,f800,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_xboole_0(X1,k2_pre_topc(X0,X2)) | ~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_xboole_0(X1,k2_pre_topc(X0,X2)) | (~v3_pre_topc(X1,X0) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X1,X0) & r1_xboole_0(X1,X2)) => r1_xboole_0(X1,k2_pre_topc(X0,X2))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tsep_1)).
% 0.22/0.51  fof(f800,plain,(
% 0.22/0.51    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | ~spl5_90),
% 0.22/0.51    inference(avatar_component_clause,[],[f798])).
% 0.22/0.51  fof(f468,plain,(
% 0.22/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | spl5_53),
% 0.22/0.51    inference(avatar_component_clause,[],[f466])).
% 0.22/0.51  fof(f571,plain,(
% 0.22/0.51    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_tarski(sK1,sK1)) | ~spl5_64),
% 0.22/0.51    inference(avatar_component_clause,[],[f569])).
% 0.22/0.51  fof(f359,plain,(
% 0.22/0.51    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_37),
% 0.22/0.51    inference(avatar_component_clause,[],[f357])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    l1_pre_topc(sK0) | ~spl5_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f105])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    v2_pre_topc(sK0) | ~spl5_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f115])).
% 0.22/0.51  fof(f801,plain,(
% 0.22/0.51    ~spl5_62 | spl5_90 | ~spl5_21 | ~spl5_61),
% 0.22/0.51    inference(avatar_split_clause,[],[f796,f543,f233,f798,f548])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    spl5_21 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.51  fof(f543,plain,(
% 0.22/0.51    spl5_61 <=> v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 0.22/0.51  fof(f796,plain,(
% 0.22/0.51    v3_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | ~m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_21 | ~spl5_61)),
% 0.22/0.51    inference(resolution,[],[f545,f234])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    ( ! [X0] : (~v4_pre_topc(X0,sK0) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f233])).
% 0.22/0.51  fof(f545,plain,(
% 0.22/0.51    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | ~spl5_61),
% 0.22/0.51    inference(avatar_component_clause,[],[f543])).
% 0.22/0.51  fof(f572,plain,(
% 0.22/0.51    spl5_64 | spl5_57),
% 0.22/0.51    inference(avatar_split_clause,[],[f562,f495,f569])).
% 0.22/0.51  fof(f495,plain,(
% 0.22/0.51    spl5_57 <=> r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 0.22/0.51  fof(f562,plain,(
% 0.22/0.51    r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_tarski(sK1,sK1)) | spl5_57),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f497,f150])).
% 0.22/0.51  fof(f150,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X1,k2_tarski(X0,X0)) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(resolution,[],[f81,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f73,f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.22/0.51  fof(f497,plain,(
% 0.22/0.51    ~r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl5_57),
% 0.22/0.51    inference(avatar_component_clause,[],[f495])).
% 0.22/0.51  fof(f552,plain,(
% 0.22/0.51    spl5_62 | ~spl5_5 | ~spl5_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f536,f164,f105,f548])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    spl5_14 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.51  fof(f536,plain,(
% 0.22/0.51    m1_subset_1(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_5 | ~spl5_14)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f166,f190])).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_5),
% 0.22/0.51    inference(resolution,[],[f80,f107])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f164])).
% 0.22/0.51  fof(f546,plain,(
% 0.22/0.51    spl5_61 | ~spl5_5 | ~spl5_7 | ~spl5_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f538,f164,f115,f105,f543])).
% 0.22/0.51  fof(f538,plain,(
% 0.22/0.51    v4_pre_topc(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),sK0) | (~spl5_5 | ~spl5_7 | ~spl5_14)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f117,f107,f166,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.22/0.51  fof(f498,plain,(
% 0.22/0.51    ~spl5_57 | ~spl5_20 | spl5_26),
% 0.22/0.51    inference(avatar_split_clause,[],[f493,f268,f220,f495])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    spl5_20 <=> k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.22/0.51  fof(f268,plain,(
% 0.22/0.51    spl5_26 <=> r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.51  fof(f493,plain,(
% 0.22/0.51    ~r2_hidden(sK1,k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl5_20 | spl5_26)),
% 0.22/0.51    inference(forward_demodulation,[],[f270,f222])).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | ~spl5_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f220])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    ~r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl5_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f268])).
% 0.22/0.51  fof(f469,plain,(
% 0.22/0.51    ~spl5_53 | spl5_51),
% 0.22/0.51    inference(avatar_split_clause,[],[f464,f452,f466])).
% 0.22/0.51  fof(f452,plain,(
% 0.22/0.51    spl5_51 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 0.22/0.51  fof(f464,plain,(
% 0.22/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK2,sK2)),k2_pre_topc(sK0,k2_tarski(sK1,sK1))) | spl5_51),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f454,f75])).
% 0.22/0.51  fof(f454,plain,(
% 0.22/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | spl5_51),
% 0.22/0.51    inference(avatar_component_clause,[],[f452])).
% 0.22/0.51  fof(f455,plain,(
% 0.22/0.51    ~spl5_51 | ~spl5_20 | spl5_45),
% 0.22/0.51    inference(avatar_split_clause,[],[f445,f408,f220,f452])).
% 0.22/0.51  fof(f408,plain,(
% 0.22/0.51    spl5_45 <=> r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.22/0.51  fof(f445,plain,(
% 0.22/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k2_tarski(sK2,sK2))) | (~spl5_20 | spl5_45)),
% 0.22/0.51    inference(backward_demodulation,[],[f410,f222])).
% 0.22/0.51  fof(f410,plain,(
% 0.22/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl5_45),
% 0.22/0.51    inference(avatar_component_clause,[],[f408])).
% 0.22/0.51  fof(f411,plain,(
% 0.22/0.51    ~spl5_45 | spl5_2 | ~spl5_19),
% 0.22/0.51    inference(avatar_split_clause,[],[f400,f215,f90,f408])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    spl5_2 <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    spl5_19 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.51  fof(f400,plain,(
% 0.22/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k2_tarski(sK1,sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | (spl5_2 | ~spl5_19)),
% 0.22/0.51    inference(backward_demodulation,[],[f92,f217])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | ~spl5_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f215])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl5_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f90])).
% 0.22/0.51  fof(f360,plain,(
% 0.22/0.51    spl5_37 | ~spl5_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f354,f143,f357])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    spl5_12 <=> r2_hidden(sK1,u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.51  fof(f354,plain,(
% 0.22/0.51    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_12),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f145,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f74,f62])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    r2_hidden(sK1,u1_struct_0(sK0)) | ~spl5_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f143])).
% 0.22/0.51  fof(f353,plain,(
% 0.22/0.51    spl5_14 | ~spl5_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f351,f134,f164])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    spl5_10 <=> r2_hidden(sK2,u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_10),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f136,f82])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    r2_hidden(sK2,u1_struct_0(sK0)) | ~spl5_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f134])).
% 0.22/0.51  fof(f350,plain,(
% 0.22/0.51    spl5_20 | ~spl5_3 | spl5_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f341,f138,f95,f220])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    spl5_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    spl5_11 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.51  fof(f341,plain,(
% 0.22/0.51    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) | (~spl5_3 | spl5_11)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f97,f139,f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(definition_unfolding,[],[f78,f62])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.51    inference(flattening,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ~v1_xboole_0(u1_struct_0(sK0)) | spl5_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f138])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl5_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f95])).
% 0.22/0.51  fof(f349,plain,(
% 0.22/0.51    spl5_19 | ~spl5_4 | spl5_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f342,f138,f100,f215])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    spl5_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | (~spl5_4 | spl5_11)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f102,f139,f83])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f100])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    spl5_10 | ~spl5_3 | spl5_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f343,f138,f95,f134])).
% 0.22/0.51  fof(f343,plain,(
% 0.22/0.51    r2_hidden(sK2,u1_struct_0(sK0)) | (~spl5_3 | spl5_11)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f97,f139,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.51  fof(f347,plain,(
% 0.22/0.51    spl5_12 | ~spl5_4 | spl5_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f344,f138,f100,f143])).
% 0.22/0.51  fof(f344,plain,(
% 0.22/0.51    r2_hidden(sK1,u1_struct_0(sK0)) | (~spl5_4 | spl5_11)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f102,f139,f76])).
% 0.22/0.51  fof(f312,plain,(
% 0.22/0.51    spl5_28 | ~spl5_11 | ~spl5_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f309,f243,f138,f282])).
% 0.22/0.51  fof(f282,plain,(
% 0.22/0.51    spl5_28 <=> v1_xboole_0(k1_connsp_2(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    spl5_22 <=> m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.51  fof(f309,plain,(
% 0.22/0.51    v1_xboole_0(k1_connsp_2(sK0,sK1)) | (~spl5_11 | ~spl5_22)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f140,f245,f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f243])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~spl5_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f138])).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    ~spl5_28 | ~spl5_16),
% 0.22/0.51    inference(avatar_split_clause,[],[f280,f198,f282])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    spl5_16 <=> r2_hidden(sK1,k1_connsp_2(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.51  fof(f280,plain,(
% 0.22/0.51    ~v1_xboole_0(k1_connsp_2(sK0,sK1)) | ~spl5_16),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f200,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(rectify,[],[f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    r2_hidden(sK1,k1_connsp_2(sK0,sK1)) | ~spl5_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f198])).
% 0.22/0.51  fof(f271,plain,(
% 0.22/0.51    ~spl5_26 | spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f259,f120,f115,f110,f105,f100,f95,f85,f268])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl5_1 <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    spl5_6 <=> v3_tdlat_3(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    spl5_8 <=> v2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    ~r2_hidden(sK1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | (spl5_1 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_7 | spl5_8)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f122,f117,f112,f107,f102,f97,f87,f64])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v3_tdlat_3(X0) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | spl5_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f85])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    v3_tdlat_3(sK0) | ~spl5_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f110])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ~v2_struct_0(sK0) | spl5_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f120])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    spl5_22 | ~spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f240,f120,f115,f105,f100,f243])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    m1_subset_1(k1_connsp_2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f122,f117,f107,f102,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    ~spl5_7 | ~spl5_5 | spl5_21 | ~spl5_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f231,f110,f233,f105,f115])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl5_6),
% 0.22/0.51    inference(resolution,[],[f66,f112])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X2,X0] : (~v3_tdlat_3(X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ! [X0] : (((v3_tdlat_3(X0) | (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK3(X0),X0) & v4_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(rectify,[],[f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.51    inference(flattening,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    spl5_16 | ~spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f196,f120,f115,f105,f100,f198])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    r2_hidden(sK1,k1_connsp_2(sK0,sK1)) | (~spl5_4 | ~spl5_5 | ~spl5_7 | spl5_8)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f122,f117,f107,f102,f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    ~spl5_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f54,f120])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ((k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f44,f43,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v3_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ? [X2] : (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) & m1_subset_1(X2,u1_struct_0(sK0))) => (k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) & ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) & ~r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f16])).
% 0.22/0.51  fof(f16,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    spl5_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f55,f115])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    spl5_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f56,f110])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    v3_tdlat_3(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    spl5_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f57,f105])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    spl5_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f58,f100])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl5_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f59,f95])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ~spl5_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f60,f90])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ~r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    ~spl5_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f61,f85])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (21824)------------------------------
% 0.22/0.51  % (21824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21824)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (21824)Memory used [KB]: 6780
% 0.22/0.51  % (21824)Time elapsed: 0.070 s
% 0.22/0.51  % (21824)------------------------------
% 0.22/0.51  % (21824)------------------------------
% 0.22/0.51  % (21833)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (21818)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (21830)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.52  % (21817)Success in time 0.154 s
%------------------------------------------------------------------------------
