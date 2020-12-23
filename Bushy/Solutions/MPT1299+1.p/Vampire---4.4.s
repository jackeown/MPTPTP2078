%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t17_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:36 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 148 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :  254 ( 516 expanded)
%              Number of equality atoms :    6 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f81,f88,f103,f105,f121,f133,f147,f152,f174,f180])).

fof(f180,plain,
    ( ~ spl4_0
    | ~ spl4_6
    | spl4_9
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f178,f96])).

fof(f96,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_6
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f178,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ spl4_0
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f175,f120])).

fof(f120,plain,
    ( k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_10
  <=> k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f175,plain,
    ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl4_0
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f73,f99,f132,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t17_tops_2.p',t16_tops_2)).

fof(f132,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_12
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f99,plain,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl4_9
  <=> ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f73,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f174,plain,
    ( ~ spl4_15
    | spl4_16
    | spl4_18
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f107,f86,f172,f166,f160])).

fof(f160,plain,
    ( spl4_15
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f166,plain,
    ( spl4_16
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f172,plain,
    ( spl4_18
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f86,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f107,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f104,f87])).

fof(f87,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f90,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t17_tops_2.p',t2_subset)).

fof(f90,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f60,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t17_tops_2.p',antisymmetry_r2_hidden)).

fof(f152,plain,
    ( ~ spl4_0
    | spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f150,f93])).

fof(f93,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_7
  <=> ~ v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f150,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f149,f120])).

fof(f149,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f148,f73])).

fof(f148,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f144,f132])).

fof(f144,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f55,f102])).

fof(f102,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_8
  <=> v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_2(X1,X0)
      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f147,plain,
    ( ~ spl4_0
    | spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f145,f93])).

fof(f145,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f143,f120])).

fof(f143,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f73,f102,f132,f55])).

fof(f133,plain,
    ( spl4_12
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f123,f86,f131])).

fof(f123,plain,
    ( m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f87,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t17_tops_2.p',dt_k7_setfam_1)).

fof(f121,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f114,f86,f119])).

fof(f114,plain,
    ( k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f87,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t17_tops_2.p',involutiveness_k7_setfam_1)).

fof(f105,plain,
    ( ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f53,f98,f92])).

fof(f53,plain,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v1_tops_2(sK1,sK0) )
    & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
      | v1_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f41,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v1_tops_2(X1,X0) )
            & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
            | ~ v1_tops_2(X1,sK0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
            | v1_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v1_tops_2(X1,X0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),sK1),X0)
          | ~ v1_tops_2(sK1,X0) )
        & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),sK1),X0)
          | v1_tops_2(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v1_tops_2(X1,X0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v1_tops_2(X1,X0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t17_tops_2.p',t17_tops_2)).

fof(f103,plain,
    ( spl4_6
    | spl4_8 ),
    inference(avatar_split_clause,[],[f52,f101,f95])).

fof(f52,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f51,f86])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f67,f79])).

fof(f79,plain,
    ( spl4_2
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f67,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f48])).

fof(f48,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK3) ),
    introduced(choice_axiom,[])).

fof(f11,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t17_tops_2.p',existence_l1_pre_topc)).

fof(f74,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f50,f72])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
