%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 333 expanded)
%              Number of leaves         :   47 ( 149 expanded)
%              Depth                    :   13
%              Number of atoms          :  548 (1007 expanded)
%              Number of equality atoms :   69 ( 134 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1190,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f69,f73,f79,f84,f88,f92,f101,f106,f115,f121,f133,f141,f145,f157,f169,f183,f282,f287,f292,f299,f365,f626,f869,f969,f1116,f1140,f1164,f1174,f1179,f1189])).

fof(f1189,plain,
    ( ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_33
    | ~ spl2_65
    | ~ spl2_95 ),
    inference(avatar_contradiction_clause,[],[f1188])).

fof(f1188,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_33
    | ~ spl2_65
    | ~ spl2_95 ),
    inference(subsumption_resolution,[],[f1187,f100])).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl2_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f1187,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_33
    | ~ spl2_65
    | ~ spl2_95 ),
    inference(forward_demodulation,[],[f1186,f105])).

fof(f105,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f1186,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_33
    | ~ spl2_65
    | ~ spl2_95 ),
    inference(subsumption_resolution,[],[f1185,f1181])).

fof(f1181,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9
    | ~ spl2_65
    | ~ spl2_95 ),
    inference(subsumption_resolution,[],[f96,f1180])).

fof(f1180,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_9
    | ~ spl2_65
    | ~ spl2_95 ),
    inference(subsumption_resolution,[],[f1175,f100])).

fof(f1175,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_65
    | ~ spl2_95 ),
    inference(superposition,[],[f625,f1173])).

fof(f1173,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)
    | ~ spl2_95 ),
    inference(avatar_component_clause,[],[f1171])).

fof(f1171,plain,
    ( spl2_95
  <=> k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).

fof(f625,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f624])).

fof(f624,plain,
    ( spl2_65
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f96,plain,
    ( ~ v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f35,f93])).

fof(f93,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(resolution,[],[f87,f78])).

fof(f78,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl2_7
  <=> ! [X0] :
        ( k2_struct_0(X0) = u1_struct_0(X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f35,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v4_pre_topc(X1,sK0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | ~ v4_pre_topc(X1,sK0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v4_pre_topc(sK1,sK0) )
      & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f1185,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_33
    | ~ spl2_95 ),
    inference(forward_demodulation,[],[f1184,f1173])).

fof(f1184,plain,
    ( v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_33 ),
    inference(forward_demodulation,[],[f1183,f105])).

fof(f1183,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_11
    | ~ spl2_33 ),
    inference(subsumption_resolution,[],[f1182,f60])).

fof(f60,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1182,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_11
    | ~ spl2_33 ),
    inference(resolution,[],[f110,f286])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X1,X0)
        | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl2_33
  <=> ! [X1,X0] :
        ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f110,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_11
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f1179,plain,
    ( ~ spl2_9
    | spl2_11
    | ~ spl2_12
    | ~ spl2_65
    | ~ spl2_95 ),
    inference(avatar_contradiction_clause,[],[f1178])).

fof(f1178,plain,
    ( $false
    | ~ spl2_9
    | spl2_11
    | ~ spl2_12
    | ~ spl2_65
    | ~ spl2_95 ),
    inference(subsumption_resolution,[],[f1177,f109])).

fof(f109,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1177,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl2_9
    | ~ spl2_12
    | ~ spl2_65
    | ~ spl2_95 ),
    inference(subsumption_resolution,[],[f1176,f100])).

fof(f1176,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_12
    | ~ spl2_65
    | ~ spl2_95 ),
    inference(subsumption_resolution,[],[f1175,f114])).

fof(f114,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl2_12
  <=> v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f1174,plain,
    ( spl2_95
    | ~ spl2_35
    | ~ spl2_87
    | ~ spl2_94 ),
    inference(avatar_split_clause,[],[f1167,f1161,f1114,f296,f1171])).

fof(f296,plain,
    ( spl2_35
  <=> k3_subset_1(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f1114,plain,
    ( spl2_87
  <=> ! [X2] : k9_subset_1(k2_struct_0(sK0),X2,k3_subset_1(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X2,k3_subset_1(k2_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f1161,plain,
    ( spl2_94
  <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).

fof(f1167,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)
    | ~ spl2_35
    | ~ spl2_87
    | ~ spl2_94 ),
    inference(forward_demodulation,[],[f1165,f298])).

fof(f298,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f296])).

fof(f1165,plain,
    ( k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)
    | ~ spl2_87
    | ~ spl2_94 ),
    inference(superposition,[],[f1163,f1115])).

fof(f1115,plain,
    ( ! [X2] : k9_subset_1(k2_struct_0(sK0),X2,k3_subset_1(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X2,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f1114])).

fof(f1163,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_94 ),
    inference(avatar_component_clause,[],[f1161])).

fof(f1164,plain,
    ( spl2_94
    | ~ spl2_9
    | ~ spl2_90 ),
    inference(avatar_split_clause,[],[f1142,f1138,f98,f1161])).

fof(f1138,plain,
    ( spl2_90
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k7_subset_1(X1,X1,X0) = k9_subset_1(X1,X1,k3_subset_1(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).

fof(f1142,plain,
    ( k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))
    | ~ spl2_9
    | ~ spl2_90 ),
    inference(resolution,[],[f1139,f100])).

fof(f1139,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k7_subset_1(X1,X1,X0) = k9_subset_1(X1,X1,k3_subset_1(X1,X0)) )
    | ~ spl2_90 ),
    inference(avatar_component_clause,[],[f1138])).

fof(f1140,plain,
    ( spl2_90
    | ~ spl2_4
    | ~ spl2_76 ),
    inference(avatar_split_clause,[],[f1032,f867,f71,f1138])).

fof(f71,plain,
    ( spl2_4
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f867,plain,
    ( spl2_76
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f1032,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | k7_subset_1(X1,X1,X0) = k9_subset_1(X1,X1,k3_subset_1(X1,X0)) )
    | ~ spl2_4
    | ~ spl2_76 ),
    inference(resolution,[],[f868,f72])).

fof(f72,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f868,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) )
    | ~ spl2_76 ),
    inference(avatar_component_clause,[],[f867])).

fof(f1116,plain,
    ( spl2_87
    | ~ spl2_9
    | ~ spl2_80 ),
    inference(avatar_split_clause,[],[f971,f967,f98,f1114])).

fof(f967,plain,
    ( spl2_80
  <=> ! [X3,X5,X4] :
        ( k9_subset_1(X3,X4,k3_subset_1(X3,X5)) = k1_setfam_1(k2_tarski(X4,k3_subset_1(X3,X5)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f971,plain,
    ( ! [X2] : k9_subset_1(k2_struct_0(sK0),X2,k3_subset_1(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X2,k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_9
    | ~ spl2_80 ),
    inference(resolution,[],[f968,f100])).

fof(f968,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(X3))
        | k9_subset_1(X3,X4,k3_subset_1(X3,X5)) = k1_setfam_1(k2_tarski(X4,k3_subset_1(X3,X5))) )
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f967])).

fof(f969,plain,
    ( spl2_80
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f148,f143,f139,f967])).

fof(f139,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f143,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f148,plain,
    ( ! [X4,X5,X3] :
        ( k9_subset_1(X3,X4,k3_subset_1(X3,X5)) = k1_setfam_1(k2_tarski(X4,k3_subset_1(X3,X5)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) )
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(resolution,[],[f144,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f144,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f143])).

fof(f869,plain,(
    spl2_76 ),
    inference(avatar_split_clause,[],[f49,f867])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f626,plain,
    ( spl2_65
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f622,f363,f103,f58,f624])).

fof(f363,plain,
    ( spl2_44
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f622,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f621,f105])).

fof(f621,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_1
    | ~ spl2_10
    | ~ spl2_44 ),
    inference(forward_demodulation,[],[f620,f105])).

fof(f620,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl2_1
    | ~ spl2_44 ),
    inference(resolution,[],[f364,f60])).

fof(f364,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(X1,X0) )
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f363])).

fof(f365,plain,(
    spl2_44 ),
    inference(avatar_split_clause,[],[f41,f363])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).

fof(f299,plain,
    ( spl2_35
    | ~ spl2_8
    | ~ spl2_15
    | ~ spl2_34 ),
    inference(avatar_split_clause,[],[f294,f289,f131,f90,f296])).

fof(f90,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f131,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k1_setfam_1(k2_tarski(X0,X1)) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f289,plain,
    ( spl2_34
  <=> r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f294,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))
    | ~ spl2_8
    | ~ spl2_15
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f293,f91])).

fof(f91,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f293,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)))
    | ~ spl2_15
    | ~ spl2_34 ),
    inference(resolution,[],[f291,f132])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_setfam_1(k2_tarski(X0,X1)) = X0 )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f131])).

fof(f291,plain,
    ( r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f289])).

fof(f292,plain,
    ( spl2_34
    | ~ spl2_21
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f283,f279,f167,f289])).

fof(f167,plain,
    ( spl2_21
  <=> ! [X3,X2] : r1_tarski(k5_xboole_0(X2,k9_subset_1(X3,X2,X3)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f279,plain,
    ( spl2_32
  <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f283,plain,
    ( r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))
    | ~ spl2_21
    | ~ spl2_32 ),
    inference(superposition,[],[f168,f281])).

fof(f281,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f279])).

fof(f168,plain,
    ( ! [X2,X3] : r1_tarski(k5_xboole_0(X2,k9_subset_1(X3,X2,X3)),X2)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f167])).

fof(f287,plain,(
    spl2_33 ),
    inference(avatar_split_clause,[],[f40,f285])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f282,plain,
    ( spl2_32
    | ~ spl2_9
    | ~ spl2_19
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f229,f181,f155,f98,f279])).

fof(f155,plain,
    ( spl2_19
  <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X0,X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f181,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f229,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1))
    | ~ spl2_9
    | ~ spl2_19
    | ~ spl2_23 ),
    inference(forward_demodulation,[],[f227,f156])).

fof(f156,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X0,X1,X0)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f155])).

fof(f227,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)))
    | ~ spl2_9
    | ~ spl2_23 ),
    inference(resolution,[],[f182,f100])).

fof(f182,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f181])).

fof(f183,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f54,f181])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f169,plain,
    ( spl2_21
    | ~ spl2_13
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f161,f155,f119,f167])).

fof(f119,plain,
    ( spl2_13
  <=> ! [X1,X0] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f161,plain,
    ( ! [X2,X3] : r1_tarski(k5_xboole_0(X2,k9_subset_1(X3,X2,X3)),X2)
    | ~ spl2_13
    | ~ spl2_19 ),
    inference(superposition,[],[f120,f156])).

fof(f120,plain,
    ( ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f157,plain,
    ( spl2_19
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f146,f143,f71,f155])).

fof(f146,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X0,X1,X0)
    | ~ spl2_4
    | ~ spl2_17 ),
    inference(resolution,[],[f144,f72])).

fof(f145,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f55,f143])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f44])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f141,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f47,f139])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f133,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f53,f131])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f121,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f52,f119])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f115,plain,
    ( spl2_11
    | spl2_12
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f95,f86,f76,f112,f108])).

fof(f95,plain,
    ( v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f34,f93])).

fof(f34,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,
    ( spl2_10
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f93,f86,f76,f103])).

fof(f101,plain,
    ( spl2_9
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f94,f86,f81,f76,f98])).

fof(f81,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f94,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f83,f93])).

fof(f83,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f92,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f43,f90])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f88,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f38,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f84,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f33,f81])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,
    ( spl2_5
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f74,f67,f58,f76])).

fof(f67,plain,
    ( spl2_3
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f74,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_1
    | ~ spl2_3 ),
    inference(resolution,[],[f68,f60])).

fof(f68,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f73,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f56,f71])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f37,f36])).

fof(f36,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f69,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f39,f67])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f61,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n016.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:43:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.41  % (12744)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.44  % (12744)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % SZS output start Proof for theBenchmark
% 0.19/0.44  fof(f1190,plain,(
% 0.19/0.44    $false),
% 0.19/0.44    inference(avatar_sat_refutation,[],[f61,f69,f73,f79,f84,f88,f92,f101,f106,f115,f121,f133,f141,f145,f157,f169,f183,f282,f287,f292,f299,f365,f626,f869,f969,f1116,f1140,f1164,f1174,f1179,f1189])).
% 0.19/0.45  fof(f1189,plain,(
% 0.19/0.45    ~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_9 | ~spl2_10 | ~spl2_11 | ~spl2_33 | ~spl2_65 | ~spl2_95),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f1188])).
% 0.19/0.45  fof(f1188,plain,(
% 0.19/0.45    $false | (~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_9 | ~spl2_10 | ~spl2_11 | ~spl2_33 | ~spl2_65 | ~spl2_95)),
% 0.19/0.45    inference(subsumption_resolution,[],[f1187,f100])).
% 0.19/0.45  fof(f100,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl2_9),
% 0.19/0.45    inference(avatar_component_clause,[],[f98])).
% 0.19/0.45  fof(f98,plain,(
% 0.19/0.45    spl2_9 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.19/0.45  fof(f1187,plain,(
% 0.19/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_9 | ~spl2_10 | ~spl2_11 | ~spl2_33 | ~spl2_65 | ~spl2_95)),
% 0.19/0.45    inference(forward_demodulation,[],[f1186,f105])).
% 0.19/0.45  fof(f105,plain,(
% 0.19/0.45    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_10),
% 0.19/0.45    inference(avatar_component_clause,[],[f103])).
% 0.19/0.45  fof(f103,plain,(
% 0.19/0.45    spl2_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.19/0.45  fof(f1186,plain,(
% 0.19/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_5 | ~spl2_7 | ~spl2_9 | ~spl2_10 | ~spl2_11 | ~spl2_33 | ~spl2_65 | ~spl2_95)),
% 0.19/0.45    inference(subsumption_resolution,[],[f1185,f1181])).
% 0.19/0.45  fof(f1181,plain,(
% 0.19/0.45    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | (~spl2_5 | ~spl2_7 | ~spl2_9 | ~spl2_65 | ~spl2_95)),
% 0.19/0.45    inference(subsumption_resolution,[],[f96,f1180])).
% 0.19/0.45  fof(f1180,plain,(
% 0.19/0.45    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0) | (~spl2_9 | ~spl2_65 | ~spl2_95)),
% 0.19/0.45    inference(subsumption_resolution,[],[f1175,f100])).
% 0.19/0.45  fof(f1175,plain,(
% 0.19/0.45    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(sK1,sK0) | (~spl2_65 | ~spl2_95)),
% 0.19/0.45    inference(superposition,[],[f625,f1173])).
% 0.19/0.45  fof(f1173,plain,(
% 0.19/0.45    k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) | ~spl2_95),
% 0.19/0.45    inference(avatar_component_clause,[],[f1171])).
% 0.19/0.45  fof(f1171,plain,(
% 0.19/0.45    spl2_95 <=> k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_95])])).
% 0.19/0.45  fof(f625,plain,(
% 0.19/0.45    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | ~spl2_65),
% 0.19/0.45    inference(avatar_component_clause,[],[f624])).
% 0.19/0.45  fof(f624,plain,(
% 0.19/0.45    spl2_65 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 0.19/0.45  fof(f96,plain,(
% 0.19/0.45    ~v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0) | (~spl2_5 | ~spl2_7)),
% 0.19/0.45    inference(backward_demodulation,[],[f35,f93])).
% 0.19/0.45  fof(f93,plain,(
% 0.19/0.45    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl2_5 | ~spl2_7)),
% 0.19/0.45    inference(resolution,[],[f87,f78])).
% 0.19/0.45  fof(f78,plain,(
% 0.19/0.45    l1_struct_0(sK0) | ~spl2_5),
% 0.19/0.45    inference(avatar_component_clause,[],[f76])).
% 0.19/0.45  fof(f76,plain,(
% 0.19/0.45    spl2_5 <=> l1_struct_0(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.45  fof(f87,plain,(
% 0.19/0.45    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl2_7),
% 0.19/0.45    inference(avatar_component_clause,[],[f86])).
% 0.19/0.45  fof(f86,plain,(
% 0.19/0.45    spl2_7 <=> ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.19/0.45  fof(f35,plain,(
% 0.19/0.45    ~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f30])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    ? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | ~v4_pre_topc(X1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v4_pre_topc(sK1,sK0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : ((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.19/0.45    inference(flattening,[],[f26])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : (((~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.19/0.45    inference(nnf_transformation,[],[f17])).
% 0.19/0.45  fof(f17,plain,(
% 0.19/0.45    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f16])).
% 0.19/0.45  fof(f16,negated_conjecture,(
% 0.19/0.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.19/0.45    inference(negated_conjecture,[],[f15])).
% 0.19/0.45  fof(f15,conjecture,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 0.19/0.45  fof(f1185,plain,(
% 0.19/0.45    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_10 | ~spl2_11 | ~spl2_33 | ~spl2_95)),
% 0.19/0.45    inference(forward_demodulation,[],[f1184,f1173])).
% 0.19/0.45  fof(f1184,plain,(
% 0.19/0.45    v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_10 | ~spl2_11 | ~spl2_33)),
% 0.19/0.45    inference(forward_demodulation,[],[f1183,f105])).
% 0.19/0.45  fof(f1183,plain,(
% 0.19/0.45    v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_1 | ~spl2_11 | ~spl2_33)),
% 0.19/0.45    inference(subsumption_resolution,[],[f1182,f60])).
% 0.19/0.45  fof(f60,plain,(
% 0.19/0.45    l1_pre_topc(sK0) | ~spl2_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f58])).
% 0.19/0.45  fof(f58,plain,(
% 0.19/0.45    spl2_1 <=> l1_pre_topc(sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.45  fof(f1182,plain,(
% 0.19/0.45    v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl2_11 | ~spl2_33)),
% 0.19/0.45    inference(resolution,[],[f110,f286])).
% 0.19/0.45  fof(f286,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_33),
% 0.19/0.45    inference(avatar_component_clause,[],[f285])).
% 0.19/0.45  fof(f285,plain,(
% 0.19/0.45    spl2_33 <=> ! [X1,X0] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.19/0.45  fof(f110,plain,(
% 0.19/0.45    v4_pre_topc(sK1,sK0) | ~spl2_11),
% 0.19/0.45    inference(avatar_component_clause,[],[f108])).
% 0.19/0.45  fof(f108,plain,(
% 0.19/0.45    spl2_11 <=> v4_pre_topc(sK1,sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.19/0.45  fof(f1179,plain,(
% 0.19/0.45    ~spl2_9 | spl2_11 | ~spl2_12 | ~spl2_65 | ~spl2_95),
% 0.19/0.45    inference(avatar_contradiction_clause,[],[f1178])).
% 0.19/0.45  fof(f1178,plain,(
% 0.19/0.45    $false | (~spl2_9 | spl2_11 | ~spl2_12 | ~spl2_65 | ~spl2_95)),
% 0.19/0.45    inference(subsumption_resolution,[],[f1177,f109])).
% 0.19/0.45  fof(f109,plain,(
% 0.19/0.45    ~v4_pre_topc(sK1,sK0) | spl2_11),
% 0.19/0.45    inference(avatar_component_clause,[],[f108])).
% 0.19/0.45  fof(f1177,plain,(
% 0.19/0.45    v4_pre_topc(sK1,sK0) | (~spl2_9 | ~spl2_12 | ~spl2_65 | ~spl2_95)),
% 0.19/0.45    inference(subsumption_resolution,[],[f1176,f100])).
% 0.19/0.45  fof(f1176,plain,(
% 0.19/0.45    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(sK1,sK0) | (~spl2_12 | ~spl2_65 | ~spl2_95)),
% 0.19/0.45    inference(subsumption_resolution,[],[f1175,f114])).
% 0.19/0.45  fof(f114,plain,(
% 0.19/0.45    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | ~spl2_12),
% 0.19/0.45    inference(avatar_component_clause,[],[f112])).
% 0.19/0.45  fof(f112,plain,(
% 0.19/0.45    spl2_12 <=> v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.19/0.45  fof(f1174,plain,(
% 0.19/0.45    spl2_95 | ~spl2_35 | ~spl2_87 | ~spl2_94),
% 0.19/0.45    inference(avatar_split_clause,[],[f1167,f1161,f1114,f296,f1171])).
% 0.19/0.45  fof(f296,plain,(
% 0.19/0.45    spl2_35 <=> k3_subset_1(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 0.19/0.45  fof(f1114,plain,(
% 0.19/0.45    spl2_87 <=> ! [X2] : k9_subset_1(k2_struct_0(sK0),X2,k3_subset_1(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X2,k3_subset_1(k2_struct_0(sK0),sK1)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 0.19/0.45  fof(f1161,plain,(
% 0.19/0.45    spl2_94 <=> k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_94])])).
% 0.19/0.45  fof(f1167,plain,(
% 0.19/0.45    k3_subset_1(k2_struct_0(sK0),sK1) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) | (~spl2_35 | ~spl2_87 | ~spl2_94)),
% 0.19/0.45    inference(forward_demodulation,[],[f1165,f298])).
% 0.19/0.45  fof(f298,plain,(
% 0.19/0.45    k3_subset_1(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) | ~spl2_35),
% 0.19/0.45    inference(avatar_component_clause,[],[f296])).
% 0.19/0.45  fof(f1165,plain,(
% 0.19/0.45    k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) = k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) | (~spl2_87 | ~spl2_94)),
% 0.19/0.45    inference(superposition,[],[f1163,f1115])).
% 0.19/0.45  fof(f1115,plain,(
% 0.19/0.45    ( ! [X2] : (k9_subset_1(k2_struct_0(sK0),X2,k3_subset_1(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X2,k3_subset_1(k2_struct_0(sK0),sK1)))) ) | ~spl2_87),
% 0.19/0.45    inference(avatar_component_clause,[],[f1114])).
% 0.19/0.45  fof(f1163,plain,(
% 0.19/0.45    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) | ~spl2_94),
% 0.19/0.45    inference(avatar_component_clause,[],[f1161])).
% 0.19/0.45  fof(f1164,plain,(
% 0.19/0.45    spl2_94 | ~spl2_9 | ~spl2_90),
% 0.19/0.45    inference(avatar_split_clause,[],[f1142,f1138,f98,f1161])).
% 0.19/0.45  fof(f1138,plain,(
% 0.19/0.45    spl2_90 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k7_subset_1(X1,X1,X0) = k9_subset_1(X1,X1,k3_subset_1(X1,X0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_90])])).
% 0.19/0.45  fof(f1142,plain,(
% 0.19/0.45    k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),sK1) = k9_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) | (~spl2_9 | ~spl2_90)),
% 0.19/0.45    inference(resolution,[],[f1139,f100])).
% 0.19/0.45  fof(f1139,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k7_subset_1(X1,X1,X0) = k9_subset_1(X1,X1,k3_subset_1(X1,X0))) ) | ~spl2_90),
% 0.19/0.45    inference(avatar_component_clause,[],[f1138])).
% 0.19/0.45  fof(f1140,plain,(
% 0.19/0.45    spl2_90 | ~spl2_4 | ~spl2_76),
% 0.19/0.45    inference(avatar_split_clause,[],[f1032,f867,f71,f1138])).
% 0.19/0.45  fof(f71,plain,(
% 0.19/0.45    spl2_4 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.45  fof(f867,plain,(
% 0.19/0.45    spl2_76 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 0.19/0.45  fof(f1032,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k7_subset_1(X1,X1,X0) = k9_subset_1(X1,X1,k3_subset_1(X1,X0))) ) | (~spl2_4 | ~spl2_76)),
% 0.19/0.45    inference(resolution,[],[f868,f72])).
% 0.19/0.45  fof(f72,plain,(
% 0.19/0.45    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl2_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f71])).
% 0.19/0.45  fof(f868,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))) ) | ~spl2_76),
% 0.19/0.45    inference(avatar_component_clause,[],[f867])).
% 0.19/0.45  fof(f1116,plain,(
% 0.19/0.45    spl2_87 | ~spl2_9 | ~spl2_80),
% 0.19/0.45    inference(avatar_split_clause,[],[f971,f967,f98,f1114])).
% 0.19/0.45  fof(f967,plain,(
% 0.19/0.45    spl2_80 <=> ! [X3,X5,X4] : (k9_subset_1(X3,X4,k3_subset_1(X3,X5)) = k1_setfam_1(k2_tarski(X4,k3_subset_1(X3,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(X3)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 0.19/0.45  fof(f971,plain,(
% 0.19/0.45    ( ! [X2] : (k9_subset_1(k2_struct_0(sK0),X2,k3_subset_1(k2_struct_0(sK0),sK1)) = k1_setfam_1(k2_tarski(X2,k3_subset_1(k2_struct_0(sK0),sK1)))) ) | (~spl2_9 | ~spl2_80)),
% 0.19/0.45    inference(resolution,[],[f968,f100])).
% 0.19/0.45  fof(f968,plain,(
% 0.19/0.45    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(X3)) | k9_subset_1(X3,X4,k3_subset_1(X3,X5)) = k1_setfam_1(k2_tarski(X4,k3_subset_1(X3,X5)))) ) | ~spl2_80),
% 0.19/0.45    inference(avatar_component_clause,[],[f967])).
% 0.19/0.45  fof(f969,plain,(
% 0.19/0.45    spl2_80 | ~spl2_16 | ~spl2_17),
% 0.19/0.45    inference(avatar_split_clause,[],[f148,f143,f139,f967])).
% 0.19/0.45  fof(f139,plain,(
% 0.19/0.45    spl2_16 <=> ! [X1,X0] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.19/0.45  fof(f143,plain,(
% 0.19/0.45    spl2_17 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.19/0.45  fof(f148,plain,(
% 0.19/0.45    ( ! [X4,X5,X3] : (k9_subset_1(X3,X4,k3_subset_1(X3,X5)) = k1_setfam_1(k2_tarski(X4,k3_subset_1(X3,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) ) | (~spl2_16 | ~spl2_17)),
% 0.19/0.45    inference(resolution,[],[f144,f140])).
% 0.19/0.45  fof(f140,plain,(
% 0.19/0.45    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_16),
% 0.19/0.45    inference(avatar_component_clause,[],[f139])).
% 0.19/0.45  fof(f144,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) ) | ~spl2_17),
% 0.19/0.45    inference(avatar_component_clause,[],[f143])).
% 0.19/0.45  fof(f869,plain,(
% 0.19/0.45    spl2_76),
% 0.19/0.45    inference(avatar_split_clause,[],[f49,f867])).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f24])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,axiom,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.19/0.45  fof(f626,plain,(
% 0.19/0.45    spl2_65 | ~spl2_1 | ~spl2_10 | ~spl2_44),
% 0.19/0.45    inference(avatar_split_clause,[],[f622,f363,f103,f58,f624])).
% 0.19/0.45  fof(f363,plain,(
% 0.19/0.45    spl2_44 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.19/0.45  fof(f622,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | v4_pre_topc(X0,sK0)) ) | (~spl2_1 | ~spl2_10 | ~spl2_44)),
% 0.19/0.45    inference(forward_demodulation,[],[f621,f105])).
% 0.19/0.45  fof(f621,plain,(
% 0.19/0.45    ( ! [X0] : (~v3_pre_topc(k7_subset_1(k2_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl2_1 | ~spl2_10 | ~spl2_44)),
% 0.19/0.45    inference(forward_demodulation,[],[f620,f105])).
% 0.19/0.45  fof(f620,plain,(
% 0.19/0.45    ( ! [X0] : (~v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl2_1 | ~spl2_44)),
% 0.19/0.45    inference(resolution,[],[f364,f60])).
% 0.19/0.45  fof(f364,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0)) ) | ~spl2_44),
% 0.19/0.45    inference(avatar_component_clause,[],[f363])).
% 0.19/0.45  fof(f365,plain,(
% 0.19/0.45    spl2_44),
% 0.19/0.45    inference(avatar_split_clause,[],[f41,f363])).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f31])).
% 0.19/0.45  fof(f31,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(nnf_transformation,[],[f20])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f13])).
% 0.19/0.45  fof(f13,axiom,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_pre_topc)).
% 0.19/0.45  fof(f299,plain,(
% 0.19/0.45    spl2_35 | ~spl2_8 | ~spl2_15 | ~spl2_34),
% 0.19/0.45    inference(avatar_split_clause,[],[f294,f289,f131,f90,f296])).
% 0.19/0.45  fof(f90,plain,(
% 0.19/0.45    spl2_8 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.45  fof(f131,plain,(
% 0.19/0.45    spl2_15 <=> ! [X1,X0] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.19/0.45  fof(f289,plain,(
% 0.19/0.45    spl2_34 <=> r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.19/0.45  fof(f294,plain,(
% 0.19/0.45    k3_subset_1(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1))) | (~spl2_8 | ~spl2_15 | ~spl2_34)),
% 0.19/0.45    inference(forward_demodulation,[],[f293,f91])).
% 0.19/0.45  fof(f91,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_8),
% 0.19/0.45    inference(avatar_component_clause,[],[f90])).
% 0.19/0.45  fof(f293,plain,(
% 0.19/0.45    k3_subset_1(k2_struct_0(sK0),sK1) = k1_setfam_1(k2_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))) | (~spl2_15 | ~spl2_34)),
% 0.19/0.45    inference(resolution,[],[f291,f132])).
% 0.19/0.45  fof(f132,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) ) | ~spl2_15),
% 0.19/0.45    inference(avatar_component_clause,[],[f131])).
% 0.19/0.45  fof(f291,plain,(
% 0.19/0.45    r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | ~spl2_34),
% 0.19/0.45    inference(avatar_component_clause,[],[f289])).
% 0.19/0.45  fof(f292,plain,(
% 0.19/0.45    spl2_34 | ~spl2_21 | ~spl2_32),
% 0.19/0.45    inference(avatar_split_clause,[],[f283,f279,f167,f289])).
% 0.19/0.45  fof(f167,plain,(
% 0.19/0.45    spl2_21 <=> ! [X3,X2] : r1_tarski(k5_xboole_0(X2,k9_subset_1(X3,X2,X3)),X2)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.19/0.45  fof(f279,plain,(
% 0.19/0.45    spl2_32 <=> k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.19/0.45  fof(f283,plain,(
% 0.19/0.45    r1_tarski(k3_subset_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) | (~spl2_21 | ~spl2_32)),
% 0.19/0.45    inference(superposition,[],[f168,f281])).
% 0.19/0.45  fof(f281,plain,(
% 0.19/0.45    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1)) | ~spl2_32),
% 0.19/0.45    inference(avatar_component_clause,[],[f279])).
% 0.19/0.45  fof(f168,plain,(
% 0.19/0.45    ( ! [X2,X3] : (r1_tarski(k5_xboole_0(X2,k9_subset_1(X3,X2,X3)),X2)) ) | ~spl2_21),
% 0.19/0.45    inference(avatar_component_clause,[],[f167])).
% 0.19/0.45  fof(f287,plain,(
% 0.19/0.45    spl2_33),
% 0.19/0.45    inference(avatar_split_clause,[],[f40,f285])).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f31])).
% 0.19/0.45  fof(f282,plain,(
% 0.19/0.45    spl2_32 | ~spl2_9 | ~spl2_19 | ~spl2_23),
% 0.19/0.45    inference(avatar_split_clause,[],[f229,f181,f155,f98,f279])).
% 0.19/0.45  fof(f155,plain,(
% 0.19/0.45    spl2_19 <=> ! [X1,X0] : k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X0,X1,X0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.19/0.45  fof(f181,plain,(
% 0.19/0.45    spl2_23 <=> ! [X1,X0] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.19/0.45  fof(f229,plain,(
% 0.19/0.45    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k9_subset_1(sK1,k2_struct_0(sK0),sK1)) | (~spl2_9 | ~spl2_19 | ~spl2_23)),
% 0.19/0.45    inference(forward_demodulation,[],[f227,f156])).
% 0.19/0.45  fof(f156,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X0,X1,X0)) ) | ~spl2_19),
% 0.19/0.45    inference(avatar_component_clause,[],[f155])).
% 0.19/0.45  fof(f227,plain,(
% 0.19/0.45    k3_subset_1(k2_struct_0(sK0),sK1) = k5_xboole_0(k2_struct_0(sK0),k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))) | (~spl2_9 | ~spl2_23)),
% 0.19/0.45    inference(resolution,[],[f182,f100])).
% 0.19/0.45  fof(f182,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) ) | ~spl2_23),
% 0.19/0.45    inference(avatar_component_clause,[],[f181])).
% 0.19/0.45  fof(f183,plain,(
% 0.19/0.45    spl2_23),
% 0.19/0.45    inference(avatar_split_clause,[],[f54,f181])).
% 0.19/0.45  fof(f54,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(definition_unfolding,[],[f48,f51])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.19/0.45    inference(definition_unfolding,[],[f45,f44])).
% 0.19/0.45  fof(f44,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f11])).
% 0.19/0.45  fof(f11,axiom,(
% 0.19/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.19/0.45  fof(f45,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.45  fof(f48,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f23])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.45  fof(f169,plain,(
% 0.19/0.45    spl2_21 | ~spl2_13 | ~spl2_19),
% 0.19/0.45    inference(avatar_split_clause,[],[f161,f155,f119,f167])).
% 0.19/0.45  fof(f119,plain,(
% 0.19/0.45    spl2_13 <=> ! [X1,X0] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.19/0.45  fof(f161,plain,(
% 0.19/0.45    ( ! [X2,X3] : (r1_tarski(k5_xboole_0(X2,k9_subset_1(X3,X2,X3)),X2)) ) | (~spl2_13 | ~spl2_19)),
% 0.19/0.45    inference(superposition,[],[f120,f156])).
% 0.19/0.45  fof(f120,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) ) | ~spl2_13),
% 0.19/0.45    inference(avatar_component_clause,[],[f119])).
% 0.19/0.45  fof(f157,plain,(
% 0.19/0.45    spl2_19 | ~spl2_4 | ~spl2_17),
% 0.19/0.45    inference(avatar_split_clause,[],[f146,f143,f71,f155])).
% 0.19/0.45  fof(f146,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = k9_subset_1(X0,X1,X0)) ) | (~spl2_4 | ~spl2_17)),
% 0.19/0.45    inference(resolution,[],[f144,f72])).
% 0.19/0.45  fof(f145,plain,(
% 0.19/0.45    spl2_17),
% 0.19/0.45    inference(avatar_split_clause,[],[f55,f143])).
% 0.19/0.45  fof(f55,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(definition_unfolding,[],[f50,f44])).
% 0.19/0.45  fof(f50,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f25])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.19/0.45  fof(f141,plain,(
% 0.19/0.45    spl2_16),
% 0.19/0.45    inference(avatar_split_clause,[],[f47,f139])).
% 0.19/0.45  fof(f47,plain,(
% 0.19/0.45    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f22])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f8])).
% 0.19/0.45  fof(f8,axiom,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.19/0.45  fof(f133,plain,(
% 0.19/0.45    spl2_15),
% 0.19/0.45    inference(avatar_split_clause,[],[f53,f131])).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f46,f44])).
% 0.19/0.45  fof(f46,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f21])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.19/0.45    inference(ennf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.19/0.45  fof(f121,plain,(
% 0.19/0.45    spl2_13),
% 0.19/0.45    inference(avatar_split_clause,[],[f52,f119])).
% 0.19/0.45  fof(f52,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f42,f51])).
% 0.19/0.45  fof(f42,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.45  fof(f115,plain,(
% 0.19/0.45    spl2_11 | spl2_12 | ~spl2_5 | ~spl2_7),
% 0.19/0.45    inference(avatar_split_clause,[],[f95,f86,f76,f112,f108])).
% 0.19/0.45  fof(f95,plain,(
% 0.19/0.45    v3_pre_topc(k3_subset_1(k2_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0) | (~spl2_5 | ~spl2_7)),
% 0.19/0.45    inference(backward_demodulation,[],[f34,f93])).
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v4_pre_topc(sK1,sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f30])).
% 0.19/0.45  fof(f106,plain,(
% 0.19/0.45    spl2_10 | ~spl2_5 | ~spl2_7),
% 0.19/0.45    inference(avatar_split_clause,[],[f93,f86,f76,f103])).
% 0.19/0.45  fof(f101,plain,(
% 0.19/0.45    spl2_9 | ~spl2_5 | ~spl2_6 | ~spl2_7),
% 0.19/0.45    inference(avatar_split_clause,[],[f94,f86,f81,f76,f98])).
% 0.19/0.45  fof(f81,plain,(
% 0.19/0.45    spl2_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.19/0.45  fof(f94,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl2_5 | ~spl2_6 | ~spl2_7)),
% 0.19/0.45    inference(backward_demodulation,[],[f83,f93])).
% 0.19/0.45  fof(f83,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_6),
% 0.19/0.45    inference(avatar_component_clause,[],[f81])).
% 0.19/0.45  fof(f92,plain,(
% 0.19/0.45    spl2_8),
% 0.19/0.45    inference(avatar_split_clause,[],[f43,f90])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.19/0.45  fof(f88,plain,(
% 0.19/0.45    spl2_7),
% 0.19/0.45    inference(avatar_split_clause,[],[f38,f86])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f12])).
% 0.19/0.45  fof(f12,axiom,(
% 0.19/0.45    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.45  fof(f84,plain,(
% 0.19/0.45    spl2_6),
% 0.19/0.45    inference(avatar_split_clause,[],[f33,f81])).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.45    inference(cnf_transformation,[],[f30])).
% 0.19/0.45  fof(f79,plain,(
% 0.19/0.45    spl2_5 | ~spl2_1 | ~spl2_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f74,f67,f58,f76])).
% 0.19/0.45  fof(f67,plain,(
% 0.19/0.45    spl2_3 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.45  fof(f74,plain,(
% 0.19/0.45    l1_struct_0(sK0) | (~spl2_1 | ~spl2_3)),
% 0.19/0.45    inference(resolution,[],[f68,f60])).
% 0.19/0.45  fof(f68,plain,(
% 0.19/0.45    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) ) | ~spl2_3),
% 0.19/0.45    inference(avatar_component_clause,[],[f67])).
% 0.19/0.45  fof(f73,plain,(
% 0.19/0.45    spl2_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f56,f71])).
% 0.19/0.45  fof(f56,plain,(
% 0.19/0.45    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(forward_demodulation,[],[f37,f36])).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0] : k2_subset_1(X0) = X0),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.19/0.45  fof(f37,plain,(
% 0.19/0.45    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,axiom,(
% 0.19/0.45    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.19/0.45  fof(f69,plain,(
% 0.19/0.45    spl2_3),
% 0.19/0.45    inference(avatar_split_clause,[],[f39,f67])).
% 0.19/0.45  fof(f39,plain,(
% 0.19/0.45    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f19])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.45    inference(ennf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,axiom,(
% 0.19/0.45    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.45  fof(f61,plain,(
% 0.19/0.45    spl2_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f32,f58])).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    l1_pre_topc(sK0)),
% 0.19/0.45    inference(cnf_transformation,[],[f30])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (12744)------------------------------
% 0.19/0.45  % (12744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (12744)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (12744)Memory used [KB]: 7419
% 0.19/0.45  % (12744)Time elapsed: 0.045 s
% 0.19/0.45  % (12744)------------------------------
% 0.19/0.45  % (12744)------------------------------
% 0.19/0.45  % (12736)Success in time 0.107 s
%------------------------------------------------------------------------------
