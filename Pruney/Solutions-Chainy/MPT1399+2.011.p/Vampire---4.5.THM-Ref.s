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
% DateTime   : Thu Dec  3 13:15:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 288 expanded)
%              Number of leaves         :   46 ( 121 expanded)
%              Depth                    :   10
%              Number of atoms          :  653 (1672 expanded)
%              Number of equality atoms :   37 ( 118 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f98,f108,f118,f134,f142,f146,f150,f154,f158,f162,f176,f180,f185,f204,f208,f222,f231,f235,f240,f252,f260,f304,f314,f319])).

fof(f319,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_27
    | spl3_30
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_27
    | spl3_30
    | ~ spl3_31
    | ~ spl3_33
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f307,f317])).

fof(f317,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_25
    | ~ spl3_27
    | ~ spl3_31
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f316,f227])).

fof(f227,plain,
    ( ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0
    | ~ spl3_13
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f225,f218])).

fof(f218,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f217,f161])).

fof(f161,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl3_18
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f217,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)
    | ~ spl3_17
    | ~ spl3_25 ),
    inference(superposition,[],[f207,f157])).

fof(f157,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl3_17
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f207,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl3_25
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f225,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_27 ),
    inference(unit_resulting_resolution,[],[f141,f221])).

fof(f221,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl3_27
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f141,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl3_13
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f316,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_31
    | ~ spl3_37 ),
    inference(unit_resulting_resolution,[],[f97,f141,f293,f251])).

fof(f251,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
        | ~ v3_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl3_31
  <=> ! [X1,X0] :
        ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
        | ~ v3_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f293,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl3_37
  <=> v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f97,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f307,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_25
    | ~ spl3_27
    | spl3_30
    | ~ spl3_33
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f242,f306])).

fof(f306,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_17
    | ~ spl3_18
    | ~ spl3_25
    | ~ spl3_27
    | ~ spl3_33
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f305,f227])).

fof(f305,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ spl3_3
    | ~ spl3_13
    | ~ spl3_33
    | ~ spl3_38 ),
    inference(unit_resulting_resolution,[],[f97,f141,f300,f259])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f258])).

fof(f258,plain,
    ( spl3_33
  <=> ! [X1,X0] :
        ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f300,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl3_38
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f242,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_24
    | spl3_30 ),
    inference(subsumption_resolution,[],[f189,f241])).

fof(f241,plain,
    ( r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_5
    | ~ spl3_24
    | spl3_30 ),
    inference(subsumption_resolution,[],[f210,f239])).

fof(f239,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl3_30
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f210,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0))
    | ~ spl3_5
    | ~ spl3_24 ),
    inference(resolution,[],[f203,f107])).

fof(f107,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1)
        | r2_hidden(X0,X1) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( r2_hidden(X0,X1)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f189,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl3_11
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f169,f186])).

fof(f186,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f133,f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X1,X0)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f133,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl3_11
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f169,plain,
    ( ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ v3_pre_topc(u1_struct_0(sK0),sK0)
    | r2_hidden(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(resolution,[],[f149,f153])).

fof(f153,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0)
        | r2_hidden(X3,k1_xboole_0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl3_16
  <=> ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f149,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_15
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f314,plain,
    ( spl3_37
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f246,f233,f140,f115,f95,f90,f291])).

fof(f90,plain,
    ( spl3_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f115,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f233,plain,
    ( spl3_29
  <=> ! [X1,X0] :
        ( v3_pre_topc(X1,X0)
        | ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f246,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_29 ),
    inference(unit_resulting_resolution,[],[f92,f97,f117,f141,f234])).

fof(f234,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(X1)
        | v3_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f233])).

fof(f117,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f92,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f304,plain,
    ( spl3_38
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f243,f229,f140,f115,f95,f90,f298])).

fof(f229,plain,
    ( spl3_28
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f243,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_28 ),
    inference(unit_resulting_resolution,[],[f92,f97,f117,f141,f230])).

fof(f230,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v1_xboole_0(X1)
        | v4_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f229])).

fof(f260,plain,(
    spl3_33 ),
    inference(avatar_split_clause,[],[f67,f258])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f252,plain,(
    spl3_31 ),
    inference(avatar_split_clause,[],[f65,f250])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f240,plain,
    ( ~ spl3_30
    | spl3_1
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f209,f182,f178,f85,f237])).

fof(f85,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f178,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f182,plain,
    ( spl3_21
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f209,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl3_1
    | ~ spl3_20
    | ~ spl3_21 ),
    inference(unit_resulting_resolution,[],[f87,f184,f179])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f178])).

fof(f184,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f87,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f235,plain,(
    spl3_29 ),
    inference(avatar_split_clause,[],[f71,f233])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f231,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f70,f229])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
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
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f222,plain,(
    spl3_27 ),
    inference(avatar_split_clause,[],[f75,f220])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f208,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f73,f206])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f204,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f74,f202])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f185,plain,
    ( spl3_21
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f167,f144,f95,f182])).

fof(f144,plain,
    ( spl3_14
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f167,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f97,f145])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f180,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f69,f178])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f176,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f76,f174])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f162,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f62,f160])).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f158,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f61,f156])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f154,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f78,f152])).

fof(f78,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f55,f56])).

fof(f56,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK0)
                    | ~ v3_pre_topc(X3,sK0) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK0)
                      & v3_pre_topc(X3,sK0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ v3_pre_topc(X3,sK0) )
                & ( ( r2_hidden(sK1,X3)
                    & v4_pre_topc(X3,sK0)
                    & v3_pre_topc(X3,sK0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ v3_pre_topc(X3,sK0) )
              & ( ( r2_hidden(sK1,X3)
                  & v4_pre_topc(X3,sK0)
                  & v3_pre_topc(X3,sK0) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK2)
              | ~ r2_hidden(sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ v3_pre_topc(X3,sK0) )
            & ( ( r2_hidden(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & v3_pre_topc(X3,sK0) )
              | ~ r2_hidden(X3,sK2) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f55,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f150,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f83,f148])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f63,f59])).

fof(f59,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f146,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f64,f144])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f142,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f60,f140])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f134,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f58,f132])).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f118,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f57,f115])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f108,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f50,f105])).

fof(f50,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f98,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f49,f95])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f93,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f48,f90])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:09:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (16465)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (16476)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (16466)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (16467)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (16475)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (16477)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (16467)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f320,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f88,f93,f98,f108,f118,f134,f142,f146,f150,f154,f158,f162,f176,f180,f185,f204,f208,f222,f231,f235,f240,f252,f260,f304,f314,f319])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    ~spl3_3 | ~spl3_5 | ~spl3_11 | ~spl3_13 | ~spl3_15 | ~spl3_16 | ~spl3_17 | ~spl3_18 | ~spl3_19 | ~spl3_24 | ~spl3_25 | ~spl3_27 | spl3_30 | ~spl3_31 | ~spl3_33 | ~spl3_37 | ~spl3_38),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f318])).
% 0.21/0.47  fof(f318,plain,(
% 0.21/0.47    $false | (~spl3_3 | ~spl3_5 | ~spl3_11 | ~spl3_13 | ~spl3_15 | ~spl3_16 | ~spl3_17 | ~spl3_18 | ~spl3_19 | ~spl3_24 | ~spl3_25 | ~spl3_27 | spl3_30 | ~spl3_31 | ~spl3_33 | ~spl3_37 | ~spl3_38)),
% 0.21/0.47    inference(subsumption_resolution,[],[f307,f317])).
% 0.21/0.47  fof(f317,plain,(
% 0.21/0.47    v4_pre_topc(u1_struct_0(sK0),sK0) | (~spl3_3 | ~spl3_13 | ~spl3_17 | ~spl3_18 | ~spl3_25 | ~spl3_27 | ~spl3_31 | ~spl3_37)),
% 0.21/0.47    inference(forward_demodulation,[],[f316,f227])).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) ) | (~spl3_13 | ~spl3_17 | ~spl3_18 | ~spl3_25 | ~spl3_27)),
% 0.21/0.47    inference(forward_demodulation,[],[f225,f218])).
% 0.21/0.47  fof(f218,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl3_17 | ~spl3_18 | ~spl3_25)),
% 0.21/0.47    inference(forward_demodulation,[],[f217,f161])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f160])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    spl3_18 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.47  fof(f217,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) ) | (~spl3_17 | ~spl3_25)),
% 0.21/0.47    inference(superposition,[],[f207,f157])).
% 0.21/0.47  fof(f157,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f156])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    spl3_17 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.47  fof(f207,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f206])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    spl3_25 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.47  fof(f225,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) ) | (~spl3_13 | ~spl3_27)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f141,f221])).
% 0.21/0.47  fof(f221,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f220])).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    spl3_27 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl3_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f140])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    spl3_13 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.47  fof(f316,plain,(
% 0.21/0.47    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) | (~spl3_3 | ~spl3_13 | ~spl3_31 | ~spl3_37)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f97,f141,f293,f251])).
% 0.21/0.47  fof(f251,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_31),
% 0.21/0.47    inference(avatar_component_clause,[],[f250])).
% 0.21/0.47  fof(f250,plain,(
% 0.21/0.47    spl3_31 <=> ! [X1,X0] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.47  fof(f293,plain,(
% 0.21/0.47    v3_pre_topc(k1_xboole_0,sK0) | ~spl3_37),
% 0.21/0.47    inference(avatar_component_clause,[],[f291])).
% 0.21/0.47  fof(f291,plain,(
% 0.21/0.47    spl3_37 <=> v3_pre_topc(k1_xboole_0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f95])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl3_3 <=> l1_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f307,plain,(
% 0.21/0.47    ~v4_pre_topc(u1_struct_0(sK0),sK0) | (~spl3_3 | ~spl3_5 | ~spl3_11 | ~spl3_13 | ~spl3_15 | ~spl3_16 | ~spl3_17 | ~spl3_18 | ~spl3_19 | ~spl3_24 | ~spl3_25 | ~spl3_27 | spl3_30 | ~spl3_33 | ~spl3_38)),
% 0.21/0.47    inference(subsumption_resolution,[],[f242,f306])).
% 0.21/0.47  fof(f306,plain,(
% 0.21/0.47    v3_pre_topc(u1_struct_0(sK0),sK0) | (~spl3_3 | ~spl3_13 | ~spl3_17 | ~spl3_18 | ~spl3_25 | ~spl3_27 | ~spl3_33 | ~spl3_38)),
% 0.21/0.47    inference(forward_demodulation,[],[f305,f227])).
% 0.21/0.47  fof(f305,plain,(
% 0.21/0.47    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) | (~spl3_3 | ~spl3_13 | ~spl3_33 | ~spl3_38)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f97,f141,f300,f259])).
% 0.21/0.47  fof(f259,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl3_33),
% 0.21/0.47    inference(avatar_component_clause,[],[f258])).
% 0.21/0.47  fof(f258,plain,(
% 0.21/0.47    spl3_33 <=> ! [X1,X0] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.47  fof(f300,plain,(
% 0.21/0.47    v4_pre_topc(k1_xboole_0,sK0) | ~spl3_38),
% 0.21/0.47    inference(avatar_component_clause,[],[f298])).
% 0.21/0.47  fof(f298,plain,(
% 0.21/0.47    spl3_38 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.47  fof(f242,plain,(
% 0.21/0.47    ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | (~spl3_5 | ~spl3_11 | ~spl3_15 | ~spl3_16 | ~spl3_19 | ~spl3_24 | spl3_30)),
% 0.21/0.47    inference(subsumption_resolution,[],[f189,f241])).
% 0.21/0.47  fof(f241,plain,(
% 0.21/0.47    r2_hidden(sK1,u1_struct_0(sK0)) | (~spl3_5 | ~spl3_24 | spl3_30)),
% 0.21/0.47    inference(subsumption_resolution,[],[f210,f239])).
% 0.21/0.47  fof(f239,plain,(
% 0.21/0.47    ~v1_xboole_0(u1_struct_0(sK0)) | spl3_30),
% 0.21/0.47    inference(avatar_component_clause,[],[f237])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    spl3_30 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,u1_struct_0(sK0)) | (~spl3_5 | ~spl3_24)),
% 0.21/0.47    inference(resolution,[],[f203,f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    spl3_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) ) | ~spl3_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f202])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    spl3_24 <=> ! [X1,X0] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | (~spl3_11 | ~spl3_15 | ~spl3_16 | ~spl3_19)),
% 0.21/0.47    inference(subsumption_resolution,[],[f169,f186])).
% 0.21/0.47  fof(f186,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_11 | ~spl3_19)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f133,f175])).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl3_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f174])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    spl3_19 <=> ! [X1,X0] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f132])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl3_11 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.47  fof(f169,plain,(
% 0.21/0.47    ~r2_hidden(sK1,u1_struct_0(sK0)) | ~v4_pre_topc(u1_struct_0(sK0),sK0) | ~v3_pre_topc(u1_struct_0(sK0),sK0) | r2_hidden(u1_struct_0(sK0),k1_xboole_0) | (~spl3_15 | ~spl3_16)),
% 0.21/0.47    inference(resolution,[],[f149,f153])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | r2_hidden(X3,k1_xboole_0)) ) | ~spl3_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f152])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl3_16 <=> ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f148])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    spl3_15 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.47  fof(f314,plain,(
% 0.21/0.47    spl3_37 | ~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_13 | ~spl3_29),
% 0.21/0.47    inference(avatar_split_clause,[],[f246,f233,f140,f115,f95,f90,f291])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl3_2 <=> v2_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl3_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f233,plain,(
% 0.21/0.47    spl3_29 <=> ! [X1,X0] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    v3_pre_topc(k1_xboole_0,sK0) | (~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_13 | ~spl3_29)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f92,f97,f117,f141,f234])).
% 0.21/0.47  fof(f234,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_29),
% 0.21/0.47    inference(avatar_component_clause,[],[f233])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f115])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    v2_pre_topc(sK0) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f90])).
% 0.21/0.47  fof(f304,plain,(
% 0.21/0.47    spl3_38 | ~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_13 | ~spl3_28),
% 0.21/0.47    inference(avatar_split_clause,[],[f243,f229,f140,f115,f95,f90,f298])).
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    spl3_28 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.47  fof(f243,plain,(
% 0.21/0.47    v4_pre_topc(k1_xboole_0,sK0) | (~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_13 | ~spl3_28)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f92,f97,f117,f141,f230])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_28),
% 0.21/0.47    inference(avatar_component_clause,[],[f229])).
% 0.21/0.47  fof(f260,plain,(
% 0.21/0.47    spl3_33),
% 0.21/0.47    inference(avatar_split_clause,[],[f67,f258])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 0.21/0.47  fof(f252,plain,(
% 0.21/0.47    spl3_31),
% 0.21/0.47    inference(avatar_split_clause,[],[f65,f250])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 0.21/0.47  fof(f240,plain,(
% 0.21/0.47    ~spl3_30 | spl3_1 | ~spl3_20 | ~spl3_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f209,f182,f178,f85,f237])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl3_1 <=> v2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    spl3_20 <=> ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    spl3_21 <=> l1_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    ~v1_xboole_0(u1_struct_0(sK0)) | (spl3_1 | ~spl3_20 | ~spl3_21)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f87,f184,f179])).
% 0.21/0.47  fof(f179,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f178])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    l1_struct_0(sK0) | ~spl3_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f182])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ~v2_struct_0(sK0) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f85])).
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    spl3_29),
% 0.21/0.47    inference(avatar_split_clause,[],[f71,f233])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).
% 0.21/0.47  fof(f231,plain,(
% 0.21/0.47    spl3_28),
% 0.21/0.47    inference(avatar_split_clause,[],[f70,f229])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    spl3_27),
% 0.21/0.47    inference(avatar_split_clause,[],[f75,f220])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    spl3_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f73,f206])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    spl3_24),
% 0.21/0.47    inference(avatar_split_clause,[],[f74,f202])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    spl3_21 | ~spl3_3 | ~spl3_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f167,f144,f95,f182])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    spl3_14 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.47  fof(f167,plain,(
% 0.21/0.47    l1_struct_0(sK0) | (~spl3_3 | ~spl3_14)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f97,f145])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) ) | ~spl3_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f144])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    spl3_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f69,f178])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    spl3_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f76,f174])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    spl3_18),
% 0.21/0.47    inference(avatar_split_clause,[],[f62,f160])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    spl3_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f61,f156])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    spl3_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f78,f152])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f55,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    k1_xboole_0 = sK2),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f43,f42,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f20])).
% 0.21/0.47  fof(f20,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    spl3_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f83,f148])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f63,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    spl3_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f64,f144])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    spl3_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f60,f140])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    spl3_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f58,f132])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f57,f115])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    v1_xboole_0(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f50,f105])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f49,f95])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f48,f90])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    ~spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f47,f85])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f44])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (16467)------------------------------
% 0.21/0.47  % (16467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16467)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (16467)Memory used [KB]: 6268
% 0.21/0.47  % (16467)Time elapsed: 0.056 s
% 0.21/0.47  % (16467)------------------------------
% 0.21/0.47  % (16467)------------------------------
% 0.21/0.47  % (16461)Success in time 0.109 s
%------------------------------------------------------------------------------
