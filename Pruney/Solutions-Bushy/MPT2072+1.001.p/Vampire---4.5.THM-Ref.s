%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2072+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 373 expanded)
%              Number of leaves         :   39 ( 138 expanded)
%              Depth                    :   15
%              Number of atoms          :  673 (1273 expanded)
%              Number of equality atoms :   46 ( 106 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f537,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f103,f108,f114,f119,f126,f140,f144,f170,f177,f238,f274,f304,f346,f352,f356,f404,f413,f421,f426,f463,f471,f535,f536])).

% (16275)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f536,plain,
    ( sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)) != k8_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 != sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
    | u1_struct_0(sK0) != k8_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | v4_pre_topc(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f535,plain,
    ( spl7_45
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f466,f460,f532])).

fof(f532,plain,
    ( spl7_45
  <=> u1_struct_0(sK0) = k8_setfam_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f460,plain,
    ( spl7_39
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f466,plain,
    ( u1_struct_0(sK0) = k8_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl7_39 ),
    inference(resolution,[],[f462,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f462,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f460])).

fof(f471,plain,
    ( spl7_40
    | ~ spl7_12
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f441,f235,f163,f468])).

fof(f468,plain,
    ( spl7_40
  <=> sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)) = k8_setfam_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f163,plain,
    ( spl7_12
  <=> sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f235,plain,
    ( spl7_21
  <=> k1_xboole_0 = sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f441,plain,
    ( sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)) = k8_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f437,f165])).

fof(f165,plain,
    ( sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f437,plain,
    ( sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)) = k8_setfam_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ spl7_21 ),
    inference(superposition,[],[f57,f237])).

fof(f237,plain,
    ( k1_xboole_0 = sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f235])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( k8_setfam_1(X0,sK6(X0,X1,X3)) = X3
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k2_cantor_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> ? [X4] :
                      ( k8_setfam_1(X0,X4) = X3
                      & v1_finset_1(X4)
                      & r1_tarski(X4,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k2_cantor_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> ? [X4] :
                      ( k8_setfam_1(X0,X4) = X3
                      & v1_finset_1(X4)
                      & r1_tarski(X4,X1)
                      & m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_cantor_1)).

fof(f463,plain,
    ( spl7_39
    | ~ spl7_12
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f438,f235,f163,f460])).

fof(f438,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_12
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f434,f165])).

fof(f434,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ spl7_21 ),
    inference(superposition,[],[f54,f237])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X3),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f426,plain,
    ( ~ spl7_3
    | spl7_7
    | ~ spl7_10
    | ~ spl7_31 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | ~ spl7_3
    | spl7_7
    | ~ spl7_10
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f424,f113])).

fof(f113,plain,
    ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl7_7
  <=> v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f424,plain,
    ( v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_31 ),
    inference(subsumption_resolution,[],[f423,f134])).

fof(f134,plain,
    ( m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_10
  <=> m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f423,plain,
    ( ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_3
    | ~ spl7_31 ),
    inference(resolution,[],[f329,f96])).

fof(f96,plain,
    ( ! [X3] :
        ( ~ v4_pre_topc(sK2(sK0,X3),sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_tops_2(X3,sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f84,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK2(X0,X1),X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> ! [X2] :
                ( v4_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f84,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f329,plain,
    ( v4_pre_topc(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl7_31
  <=> v4_pre_topc(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f421,plain,
    ( ~ spl7_12
    | ~ spl7_30
    | spl7_31 ),
    inference(avatar_contradiction_clause,[],[f420])).

fof(f420,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_30
    | spl7_31 ),
    inference(subsumption_resolution,[],[f419,f165])).

fof(f419,plain,
    ( ~ sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ spl7_30
    | spl7_31 ),
    inference(subsumption_resolution,[],[f418,f330])).

fof(f330,plain,
    ( ~ v4_pre_topc(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK0)
    | spl7_31 ),
    inference(avatar_component_clause,[],[f328])).

fof(f418,plain,
    ( v4_pre_topc(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ spl7_30 ),
    inference(superposition,[],[f320,f57])).

fof(f320,plain,
    ( v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl7_30
  <=> v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f413,plain,
    ( spl7_21
    | ~ spl7_24
    | ~ spl7_29
    | spl7_30 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | spl7_21
    | ~ spl7_24
    | ~ spl7_29
    | spl7_30 ),
    inference(subsumption_resolution,[],[f411,f263])).

fof(f263,plain,
    ( m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl7_24
  <=> m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f411,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl7_21
    | ~ spl7_29
    | spl7_30 ),
    inference(subsumption_resolution,[],[f410,f236])).

fof(f236,plain,
    ( k1_xboole_0 != sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
    | spl7_21 ),
    inference(avatar_component_clause,[],[f235])).

fof(f410,plain,
    ( k1_xboole_0 = sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_29
    | spl7_30 ),
    inference(subsumption_resolution,[],[f409,f321])).

fof(f321,plain,
    ( ~ v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | spl7_30 ),
    inference(avatar_component_clause,[],[f319])).

fof(f409,plain,
    ( v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | k1_xboole_0 = sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_29 ),
    inference(superposition,[],[f303,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f303,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl7_29
  <=> v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f404,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6
    | spl7_23
    | ~ spl7_33 ),
    inference(avatar_contradiction_clause,[],[f403])).

fof(f403,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6
    | spl7_23
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f402,f89])).

fof(f89,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_4
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f402,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | ~ spl7_3
    | ~ spl7_6
    | spl7_23
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f401,f259])).

fof(f259,plain,
    ( ~ v4_pre_topc(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl7_23
  <=> v4_pre_topc(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f401,plain,
    ( v4_pre_topc(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ v2_tops_2(sK1,sK0)
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f398,f107])).

fof(f107,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f398,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ v2_tops_2(sK1,sK0)
    | ~ spl7_3
    | ~ spl7_33 ),
    inference(resolution,[],[f345,f98])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v4_pre_topc(X1,sK0)
        | ~ v2_tops_2(X0,sK0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f94,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,X0)
        | v4_pre_topc(X1,sK0)
        | ~ v2_tops_2(X0,sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f84,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X1)
      | v4_pre_topc(X2,X0)
      | ~ v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f345,plain,
    ( r2_hidden(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl7_33
  <=> r2_hidden(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f356,plain,
    ( ~ spl7_12
    | spl7_34 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | ~ spl7_12
    | spl7_34 ),
    inference(subsumption_resolution,[],[f353,f165])).

fof(f353,plain,
    ( ~ sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | spl7_34 ),
    inference(resolution,[],[f351,f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(sK6(X0,X1,X3),X1)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f351,plain,
    ( ~ r1_tarski(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),sK1)
    | spl7_34 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl7_34
  <=> r1_tarski(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f352,plain,
    ( ~ spl7_34
    | spl7_32 ),
    inference(avatar_split_clause,[],[f347,f339,f349])).

fof(f339,plain,
    ( spl7_32
  <=> m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f347,plain,
    ( ~ r1_tarski(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),sK1)
    | spl7_32 ),
    inference(resolution,[],[f341,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f341,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(sK1))
    | spl7_32 ),
    inference(avatar_component_clause,[],[f339])).

fof(f346,plain,
    ( ~ spl7_32
    | spl7_33
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f267,f231,f163,f343,f339])).

fof(f231,plain,
    ( spl7_20
  <=> r2_hidden(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f267,plain,
    ( r2_hidden(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK1)
    | ~ m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(sK1))
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(resolution,[],[f252,f243])).

fof(f243,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),X1)
        | ~ m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(X1)) )
    | ~ spl7_20 ),
    inference(resolution,[],[f233,f65])).

fof(f233,plain,
    ( r2_hidden(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f231])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(X0,sK1) )
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f250,f165])).

fof(f250,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,sK1)
        | ~ sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0)) )
    | ~ spl7_20 ),
    inference(resolution,[],[f247,f55])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),X1)
        | r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,X1) )
    | ~ spl7_20 ),
    inference(resolution,[],[f246,f63])).

fof(f246,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | r2_hidden(X1,X0) )
    | ~ spl7_20 ),
    inference(resolution,[],[f242,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f242,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(X0)) )
    | ~ spl7_20 ),
    inference(resolution,[],[f233,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f304,plain,
    ( spl7_29
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_23
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f299,f262,f258,f82,f77,f301])).

fof(f77,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f299,plain,
    ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_23
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f298,f263])).

fof(f298,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_23 ),
    inference(resolution,[],[f260,f131])).

fof(f131,plain,
    ( ! [X1] :
        ( ~ v4_pre_topc(sK3(sK0,X1),sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X1),sK0) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f92,f84])).

fof(f92,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v4_pre_topc(sK3(sK0,X1),sK0)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X1),sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f79,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v4_pre_topc(sK3(X0,X1),X0)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0)
          | ? [X2] :
              ( ~ v4_pre_topc(X2,X0)
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v4_pre_topc(X2,X0) ) )
           => v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_pre_topc)).

fof(f79,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f260,plain,
    ( v4_pre_topc(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK0)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f258])).

fof(f274,plain,
    ( ~ spl7_12
    | spl7_24 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl7_12
    | spl7_24 ),
    inference(subsumption_resolution,[],[f271,f165])).

fof(f271,plain,
    ( ~ sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | spl7_24 ),
    inference(resolution,[],[f264,f54])).

fof(f264,plain,
    ( ~ m1_subset_1(sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl7_24 ),
    inference(avatar_component_clause,[],[f262])).

fof(f238,plain,
    ( spl7_20
    | spl7_21
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f186,f163,f133,f111,f82,f77,f235,f231])).

fof(f186,plain,
    ( k1_xboole_0 = sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
    | r2_hidden(sK3(sK0,sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK6(u1_struct_0(sK0),sK1,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1))))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(resolution,[],[f184,f165])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),X0,u1_struct_0(sK0))
        | k1_xboole_0 = sK6(u1_struct_0(sK0),X0,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
        | r2_hidden(sK3(sK0,sK6(u1_struct_0(sK0),X0,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK6(u1_struct_0(sK0),X0,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))) )
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f183,f134])).

fof(f183,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK6(u1_struct_0(sK0),X0,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))
        | ~ sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r2_hidden(sK3(sK0,sK6(u1_struct_0(sK0),X0,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))),sK6(u1_struct_0(sK0),X0,sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)))) )
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7 ),
    inference(resolution,[],[f181,f113])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( v2_tops_2(X1,sK0)
        | k1_xboole_0 = sK6(u1_struct_0(sK0),X0,sK2(sK0,X1))
        | ~ sP5(sK2(sK0,X1),X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r2_hidden(sK3(sK0,sK6(u1_struct_0(sK0),X0,sK2(sK0,X1))),sK6(u1_struct_0(sK0),X0,sK2(sK0,X1))) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f153,f96])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(X1,sK0)
        | r2_hidden(sK3(sK0,sK6(u1_struct_0(sK0),X0,X1)),sK6(u1_struct_0(sK0),X0,X1))
        | k1_xboole_0 = sK6(u1_struct_0(sK0),X0,X1)
        | ~ sP5(X1,X0,u1_struct_0(sK0)) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f152,f54])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(X1,sK0)
        | r2_hidden(sK3(sK0,sK6(u1_struct_0(sK0),X0,X1)),sK6(u1_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(sK6(u1_struct_0(sK0),X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = sK6(u1_struct_0(sK0),X0,X1)
        | ~ sP5(X1,X0,u1_struct_0(sK0)) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(superposition,[],[f130,f57])).

fof(f130,plain,
    ( ! [X0] :
        ( v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),X0),sK0)
        | r2_hidden(sK3(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X0 )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( ! [X0] :
        ( v4_pre_topc(k8_setfam_1(u1_struct_0(sK0),X0),sK0)
        | r2_hidden(sK3(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(superposition,[],[f128,f52])).

fof(f128,plain,
    ( ! [X0] :
        ( v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0)
        | r2_hidden(sK3(sK0,X0),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f91,f84])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | r2_hidden(sK3(sK0,X0),X0)
        | v4_pre_topc(k6_setfam_1(u1_struct_0(sK0),X0),sK0) )
    | ~ spl7_2 ),
    inference(resolution,[],[f79,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK3(X0,X1),X1)
      | v4_pre_topc(k6_setfam_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f177,plain,
    ( ~ spl7_3
    | spl7_7
    | ~ spl7_10
    | spl7_13 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl7_3
    | spl7_7
    | ~ spl7_10
    | spl7_13 ),
    inference(subsumption_resolution,[],[f175,f113])).

fof(f175,plain,
    ( v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_3
    | ~ spl7_10
    | spl7_13 ),
    inference(subsumption_resolution,[],[f174,f84])).

fof(f174,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl7_10
    | spl7_13 ),
    inference(subsumption_resolution,[],[f171,f134])).

fof(f171,plain,
    ( ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0)
    | spl7_13 ),
    inference(resolution,[],[f169,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f169,plain,
    ( ~ m1_subset_1(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl7_13
  <=> m1_subset_1(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f170,plain,
    ( spl7_12
    | ~ spl7_13
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f150,f137,f133,f105,f167,f163])).

fof(f137,plain,
    ( spl7_11
  <=> r2_hidden(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k2_cantor_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f150,plain,
    ( ~ m1_subset_1(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ spl7_6
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f149,f107])).

fof(f149,plain,
    ( ~ m1_subset_1(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f145,f134])).

fof(f145,plain,
    ( ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | sP5(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_11 ),
    inference(resolution,[],[f139,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_cantor_1(X0,X1))
      | ~ m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | sP5(X3,X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_cantor_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f139,plain,
    ( r2_hidden(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k2_cantor_1(u1_struct_0(sK0),sK1))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f144,plain,
    ( ~ spl7_6
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl7_6
    | spl7_10 ),
    inference(subsumption_resolution,[],[f141,f107])).

fof(f141,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl7_10 ),
    inference(resolution,[],[f135,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k2_cantor_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_cantor_1)).

fof(f135,plain,
    ( ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f140,plain,
    ( ~ spl7_10
    | spl7_11
    | ~ spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f127,f111,f82,f137,f133])).

fof(f127,plain,
    ( r2_hidden(sK2(sK0,k2_cantor_1(u1_struct_0(sK0),sK1)),k2_cantor_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_cantor_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl7_3
    | spl7_7 ),
    inference(resolution,[],[f95,f113])).

fof(f95,plain,
    ( ! [X2] :
        ( v2_tops_2(X2,sK0)
        | r2_hidden(sK2(sK0,X2),X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl7_3 ),
    inference(resolution,[],[f84,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(sK2(X0,X1),X1)
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f126,plain,
    ( spl7_9
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f121,f116,f82,f77,f123])).

fof(f123,plain,
    ( spl7_9
  <=> v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f116,plain,
    ( spl7_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f121,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f120,f118])).

fof(f118,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f116])).

fof(f120,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f93,f84])).

fof(f93,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f79,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f119,plain,
    ( spl7_8
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f109,f100,f116])).

fof(f100,plain,
    ( spl7_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f109,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl7_5 ),
    inference(resolution,[],[f102,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f102,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f114,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f35,f111])).

fof(f35,plain,(
    ~ v2_tops_2(k2_cantor_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0)
          & v2_tops_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
             => v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
           => v2_tops_2(k2_cantor_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_yellow19)).

fof(f108,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f33,f105])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,
    ( spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f97,f82,f100])).

fof(f97,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f84,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f90,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f34,f87])).

fof(f34,plain,(
    v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f85,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f37,f77])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
