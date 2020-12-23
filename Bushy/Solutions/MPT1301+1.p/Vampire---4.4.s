%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t19_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:36 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 451 expanded)
%              Number of leaves         :   47 ( 184 expanded)
%              Depth                    :   12
%              Number of atoms          :  475 (1453 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f403,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f86,f93,f100,f107,f114,f121,f129,f155,f163,f183,f191,f207,f214,f229,f236,f250,f260,f272,f279,f286,f293,f300,f336,f348,f355,f374,f381,f388,f395,f402])).

fof(f402,plain,
    ( spl6_23
    | ~ spl6_56
    | spl6_59 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | ~ spl6_23
    | ~ spl6_56
    | ~ spl6_59 ),
    inference(subsumption_resolution,[],[f400,f394])).

fof(f394,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK2)
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl6_59
  <=> ~ r2_hidden(sK3(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f400,plain,
    ( r2_hidden(sK3(sK0,sK1),sK2)
    | ~ spl6_23
    | ~ spl6_56 ),
    inference(unit_resulting_resolution,[],[f190,f387,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t19_tops_2.p',t2_subset)).

fof(f387,plain,
    ( m1_subset_1(sK3(sK0,sK1),sK2)
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f386])).

fof(f386,plain,
    ( spl6_56
  <=> m1_subset_1(sK3(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f190,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl6_23
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f395,plain,
    ( ~ spl6_59
    | ~ spl6_0
    | ~ spl6_6
    | spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f340,f119,f112,f105,f98,f77,f393])).

fof(f77,plain,
    ( spl6_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f98,plain,
    ( spl6_6
  <=> v2_tops_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f105,plain,
    ( spl6_9
  <=> ~ v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f112,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f119,plain,
    ( spl6_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f340,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK2)
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(unit_resulting_resolution,[],[f78,f99,f106,f113,f120,f241])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( v2_tops_2(X1,X0)
      | ~ v2_tops_2(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(sK3(X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(subsumption_resolution,[],[f240,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t19_tops_2.p',t4_subset)).

fof(f240,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X2)
      | ~ m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X2)
      | ~ m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f59,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(sK3(X0,X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ( ~ v4_pre_topc(sK3(X0,X1),X0)
                & r2_hidden(sK3(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v4_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK3(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v4_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v4_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v4_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/tops_2__t19_tops_2.p',d2_tops_2)).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( v4_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f113,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f112])).

fof(f106,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f99,plain,
    ( v2_tops_2(sK2,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f78,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f77])).

fof(f388,plain,
    ( spl6_56
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f169,f161,f127,f386])).

fof(f127,plain,
    ( spl6_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f161,plain,
    ( spl6_18
  <=> r2_hidden(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f169,plain,
    ( m1_subset_1(sK3(sK0,sK1),sK2)
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f128,f162,f70])).

fof(f162,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f128,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f381,plain,
    ( spl6_54
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f166,f161,f379])).

fof(f379,plain,
    ( spl6_54
  <=> m1_subset_1(sK3(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f166,plain,
    ( m1_subset_1(sK3(sK0,sK1),sK1)
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f162,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t19_tops_2.p',t1_subset)).

fof(f374,plain,
    ( ~ spl6_53
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f165,f161,f372])).

fof(f372,plain,
    ( spl6_53
  <=> ~ r2_hidden(sK1,sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f165,plain,
    ( ~ r2_hidden(sK1,sK3(sK0,sK1))
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f162,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t19_tops_2.p',antisymmetry_r2_hidden)).

fof(f355,plain,
    ( spl6_50
    | spl6_23
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f338,f334,f189,f353])).

fof(f353,plain,
    ( spl6_50
  <=> r2_hidden(sK4(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f334,plain,
    ( spl6_46
  <=> m1_subset_1(sK4(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f338,plain,
    ( r2_hidden(sK4(sK1),sK2)
    | ~ spl6_23
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f190,f335,f66])).

fof(f335,plain,
    ( m1_subset_1(sK4(sK1),sK2)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f334])).

fof(f348,plain,
    ( ~ spl6_49
    | spl6_23
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f337,f334,f189,f346])).

fof(f346,plain,
    ( spl6_49
  <=> ~ r2_hidden(sK2,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f337,plain,
    ( ~ r2_hidden(sK2,sK4(sK1))
    | ~ spl6_23
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f190,f335,f131])).

fof(f131,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f66,f64])).

fof(f336,plain,
    ( spl6_46
    | ~ spl6_14
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f310,f284,f127,f334])).

fof(f284,plain,
    ( spl6_40
  <=> r2_hidden(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f310,plain,
    ( m1_subset_1(sK4(sK1),sK2)
    | ~ spl6_14
    | ~ spl6_40 ),
    inference(unit_resulting_resolution,[],[f128,f285,f70])).

fof(f285,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f284])).

fof(f300,plain,
    ( spl6_44
    | spl6_23 ),
    inference(avatar_split_clause,[],[f199,f189,f298])).

fof(f298,plain,
    ( spl6_44
  <=> r2_hidden(sK4(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f199,plain,
    ( r2_hidden(sK4(sK2),sK2)
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f63,f190,f66])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f13,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t19_tops_2.p',existence_m1_subset_1)).

fof(f293,plain,
    ( ~ spl6_43
    | spl6_23 ),
    inference(avatar_split_clause,[],[f198,f189,f291])).

fof(f291,plain,
    ( spl6_43
  <=> ~ r2_hidden(sK2,sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f198,plain,
    ( ~ r2_hidden(sK2,sK4(sK2))
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f63,f190,f131])).

fof(f286,plain,
    ( spl6_40
    | spl6_21 ),
    inference(avatar_split_clause,[],[f194,f181,f284])).

fof(f181,plain,
    ( spl6_21
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f194,plain,
    ( r2_hidden(sK4(sK1),sK1)
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f63,f182,f66])).

fof(f182,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f181])).

fof(f279,plain,
    ( ~ spl6_39
    | spl6_21 ),
    inference(avatar_split_clause,[],[f193,f181,f277])).

fof(f277,plain,
    ( spl6_39
  <=> ~ r2_hidden(sK1,sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f193,plain,
    ( ~ r2_hidden(sK1,sK4(sK1))
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f63,f182,f131])).

fof(f272,plain,
    ( ~ spl6_37
    | ~ spl6_0
    | spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f184,f112,f105,f77,f270])).

fof(f270,plain,
    ( spl6_37
  <=> ~ v4_pre_topc(sK3(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f184,plain,
    ( ~ v4_pre_topc(sK3(sK0,sK1),sK0)
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f78,f106,f113,f62])).

fof(f260,plain,
    ( ~ spl6_35
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f170,f161,f112,f258])).

fof(f258,plain,
    ( spl6_35
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f170,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f113,f162,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t19_tops_2.p',t5_subset)).

fof(f250,plain,
    ( ~ spl6_33
    | spl6_17
    | spl6_21 ),
    inference(avatar_split_clause,[],[f195,f181,f153,f248])).

fof(f248,plain,
    ( spl6_33
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f153,plain,
    ( spl6_17
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f195,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl6_17
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f154,f182,f66])).

fof(f154,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f236,plain,
    ( ~ spl6_31
    | spl6_27 ),
    inference(avatar_split_clause,[],[f221,f212,f234])).

fof(f234,plain,
    ( spl6_31
  <=> ~ r2_hidden(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f212,plain,
    ( spl6_27
  <=> ~ m1_subset_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f221,plain,
    ( ~ r2_hidden(sK2,sK2)
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f213,f65])).

fof(f213,plain,
    ( ~ m1_subset_1(sK2,sK2)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f212])).

fof(f229,plain,
    ( ~ spl6_29
    | spl6_25 ),
    inference(avatar_split_clause,[],[f217,f205,f227])).

fof(f227,plain,
    ( spl6_29
  <=> ~ r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f205,plain,
    ( spl6_25
  <=> ~ m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f217,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ spl6_25 ),
    inference(unit_resulting_resolution,[],[f206,f65])).

fof(f206,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f205])).

fof(f214,plain,
    ( ~ spl6_27
    | spl6_23 ),
    inference(avatar_split_clause,[],[f197,f189,f212])).

fof(f197,plain,
    ( ~ m1_subset_1(sK2,sK2)
    | ~ spl6_23 ),
    inference(unit_resulting_resolution,[],[f190,f138])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f131,f66])).

fof(f207,plain,
    ( ~ spl6_25
    | spl6_21 ),
    inference(avatar_split_clause,[],[f192,f181,f205])).

fof(f192,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f182,f138])).

fof(f191,plain,
    ( ~ spl6_23
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f171,f161,f127,f189])).

fof(f171,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f128,f162,f71])).

fof(f183,plain,
    ( ~ spl6_21
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f167,f161,f181])).

fof(f167,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f162,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t19_tops_2.p',t7_boole)).

fof(f163,plain,
    ( spl6_18
    | ~ spl6_0
    | spl6_9
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f147,f112,f105,f77,f161])).

fof(f147,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | ~ spl6_0
    | ~ spl6_9
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f78,f106,f113,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_tops_2(X1,X0)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f155,plain,
    ( ~ spl6_17
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f144,f127,f153])).

fof(f144,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f128,f141])).

fof(f141,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f140,f71])).

fof(f140,plain,(
    ! [X2,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f138,f70])).

fof(f129,plain,
    ( spl6_14
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f122,f91,f127])).

fof(f91,plain,
    ( spl6_4
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f122,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f92,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t19_tops_2.p',t3_subset)).

fof(f92,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f121,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f54,f119])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ v2_tops_2(sK1,sK0)
    & v2_tops_2(sK2,sK0)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_2(X1,X0)
                & v2_tops_2(X2,X0)
                & r1_tarski(X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,sK0)
              & v2_tops_2(X2,sK0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,X0)
              & v2_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ~ v2_tops_2(sK1,X0)
            & v2_tops_2(X2,X0)
            & r1_tarski(sK1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tops_2(X1,X0)
          & v2_tops_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ v2_tops_2(X1,X0)
        & v2_tops_2(sK2,X0)
        & r1_tarski(X1,sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,X0)
              & v2_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_2(X1,X0)
              & v2_tops_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( ( v2_tops_2(X2,X0)
                    & r1_tarski(X1,X2) )
                 => v2_tops_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( ( v2_tops_2(X2,X0)
                  & r1_tarski(X1,X2) )
               => v2_tops_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t19_tops_2.p',t19_tops_2)).

fof(f114,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f53,f112])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f107,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f57,f105])).

fof(f57,plain,(
    ~ v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f56,f98])).

fof(f56,plain,(
    v2_tops_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f93,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f55,f91])).

fof(f55,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f72,f84])).

fof(f84,plain,
    ( spl6_2
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f72,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f11,f50])).

fof(f50,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK5) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t19_tops_2.p',existence_l1_pre_topc)).

fof(f79,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f52,f77])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
