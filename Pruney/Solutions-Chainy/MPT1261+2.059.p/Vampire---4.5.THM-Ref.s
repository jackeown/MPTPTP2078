%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 332 expanded)
%              Number of leaves         :   50 ( 160 expanded)
%              Depth                    :   11
%              Number of atoms          :  533 (1090 expanded)
%              Number of equality atoms :  113 ( 245 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1677,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f86,f92,f100,f104,f108,f112,f116,f124,f142,f148,f160,f164,f180,f189,f197,f213,f227,f248,f255,f314,f319,f345,f356,f429,f542,f640,f696,f897,f1117,f1130,f1378,f1582,f1676])).

fof(f1676,plain,
    ( spl2_28
    | ~ spl2_68
    | ~ spl2_140 ),
    inference(avatar_contradiction_clause,[],[f1675])).

fof(f1675,plain,
    ( $false
    | spl2_28
    | ~ spl2_68
    | ~ spl2_140 ),
    inference(subsumption_resolution,[],[f247,f1671])).

fof(f1671,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_68
    | ~ spl2_140 ),
    inference(superposition,[],[f1581,f639])).

fof(f639,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_68 ),
    inference(avatar_component_clause,[],[f637])).

fof(f637,plain,
    ( spl2_68
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).

fof(f1581,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_140 ),
    inference(avatar_component_clause,[],[f1579])).

fof(f1579,plain,
    ( spl2_140
  <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_140])])).

fof(f247,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | spl2_28 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl2_28
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f1582,plain,
    ( spl2_140
    | ~ spl2_9
    | ~ spl2_131 ),
    inference(avatar_split_clause,[],[f1478,f1375,f102,f1579])).

fof(f102,plain,
    ( spl2_9
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f1375,plain,
    ( spl2_131
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_131])])).

fof(f1478,plain,
    ( sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_9
    | ~ spl2_131 ),
    inference(superposition,[],[f103,f1377])).

fof(f1377,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_131 ),
    inference(avatar_component_clause,[],[f1375])).

fof(f103,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f1378,plain,
    ( spl2_131
    | ~ spl2_120
    | ~ spl2_121 ),
    inference(avatar_split_clause,[],[f1183,f1127,f1115,f1375])).

fof(f1115,plain,
    ( spl2_120
  <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).

fof(f1127,plain,
    ( spl2_121
  <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).

fof(f1183,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_120
    | ~ spl2_121 ),
    inference(superposition,[],[f1129,f1116])).

fof(f1116,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_120 ),
    inference(avatar_component_clause,[],[f1115])).

fof(f1129,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_121 ),
    inference(avatar_component_clause,[],[f1127])).

fof(f1130,plain,
    ( spl2_121
    | ~ spl2_14
    | ~ spl2_62 ),
    inference(avatar_split_clause,[],[f545,f539,f122,f1127])).

fof(f122,plain,
    ( spl2_14
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f539,plain,
    ( spl2_62
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).

fof(f545,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_14
    | ~ spl2_62 ),
    inference(unit_resulting_resolution,[],[f541,f123])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f122])).

fof(f541,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_62 ),
    inference(avatar_component_clause,[],[f539])).

fof(f1117,plain,
    ( spl2_120
    | ~ spl2_12
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f359,f354,f114,f1115])).

fof(f114,plain,
    ( spl2_12
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f354,plain,
    ( spl2_44
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f359,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_12
    | ~ spl2_44 ),
    inference(superposition,[],[f355,f115])).

fof(f115,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f355,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f354])).

fof(f897,plain,
    ( ~ spl2_16
    | ~ spl2_2
    | ~ spl2_4
    | spl2_36
    | ~ spl2_29
    | ~ spl2_37
    | ~ spl2_53 ),
    inference(avatar_split_clause,[],[f673,f427,f316,f253,f311,f79,f69,f139])).

fof(f139,plain,
    ( spl2_16
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f69,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f79,plain,
    ( spl2_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f311,plain,
    ( spl2_36
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f253,plain,
    ( spl2_29
  <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f316,plain,
    ( spl2_37
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f427,plain,
    ( spl2_53
  <=> ! [X1,X0] :
        ( ~ v4_pre_topc(X0,X1)
        | k2_pre_topc(X1,X0) = X0
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f673,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_29
    | ~ spl2_37
    | ~ spl2_53 ),
    inference(forward_demodulation,[],[f435,f254])).

fof(f254,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f253])).

fof(f435,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_37
    | ~ spl2_53 ),
    inference(superposition,[],[f318,f428])).

fof(f428,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X1,X0) = X0
        | ~ v4_pre_topc(X0,X1)
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) )
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f427])).

fof(f318,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f316])).

fof(f696,plain,
    ( ~ spl2_4
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f694,f311,f253,f79])).

fof(f694,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_29
    | ~ spl2_36 ),
    inference(subsumption_resolution,[],[f672,f313])).

fof(f313,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f311])).

fof(f672,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f43,f254])).

fof(f43,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f640,plain,
    ( spl2_68
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_21
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f243,f224,f195,f178,f74,f69,f637])).

fof(f74,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f178,plain,
    ( spl2_21
  <=> ! [X1,X0,X2] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f195,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f224,plain,
    ( spl2_27
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f243,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_21
    | ~ spl2_23
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f235,f199])).

fof(f199,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(unit_resulting_resolution,[],[f71,f76,f196])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f71,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f235,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(unit_resulting_resolution,[],[f76,f226,f179])).

fof(f179,plain,
    ( ! [X2,X0,X1] :
        ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f178])).

fof(f226,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f224])).

fof(f542,plain,
    ( spl2_62
    | ~ spl2_36
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f536,f343,f311,f539])).

fof(f343,plain,
    ( spl2_42
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f536,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_36
    | ~ spl2_42 ),
    inference(superposition,[],[f344,f313])).

fof(f344,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f343])).

fof(f429,plain,
    ( spl2_53
    | ~ spl2_11
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f181,f162,f110,f427])).

fof(f110,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f162,plain,
    ( spl2_20
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( ~ v4_pre_topc(X0,X1)
        | k2_pre_topc(X1,X0) = X0
        | ~ l1_pre_topc(X1)
        | ~ r1_tarski(X0,u1_struct_0(X1)) )
    | ~ spl2_11
    | ~ spl2_20 ),
    inference(resolution,[],[f163,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) = X1
        | ~ l1_pre_topc(X0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f162])).

fof(f356,plain,
    ( spl2_44
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f134,f114,f98,f354])).

fof(f98,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f134,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_8
    | ~ spl2_12 ),
    inference(superposition,[],[f115,f99])).

fof(f99,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f345,plain,
    ( spl2_42
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f126,f106,f90,f343])).

fof(f90,plain,
    ( spl2_6
  <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f106,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f126,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_6
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f91,f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f91,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f319,plain,
    ( spl2_37
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f214,f211,f74,f69,f316])).

fof(f211,plain,
    ( spl2_25
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f214,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_25 ),
    inference(unit_resulting_resolution,[],[f71,f76,f212])).

fof(f212,plain,
    ( ! [X0,X1] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f211])).

fof(f314,plain,
    ( ~ spl2_3
    | spl2_36
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f151,f146,f83,f311,f74])).

fof(f83,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f146,plain,
    ( spl2_17
  <=> ! [X1,X0,X2] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f151,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | ~ spl2_17 ),
    inference(superposition,[],[f147,f85])).

fof(f85,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f146])).

fof(f255,plain,
    ( spl2_29
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f149,f146,f74,f253])).

fof(f149,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(unit_resulting_resolution,[],[f76,f147])).

fof(f248,plain,
    ( ~ spl2_28
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_22 ),
    inference(avatar_split_clause,[],[f198,f187,f79,f74,f69,f64,f245])).

fof(f64,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f187,plain,
    ( spl2_22
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | k2_pre_topc(X0,X1) != X1
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f198,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_22 ),
    inference(unit_resulting_resolution,[],[f71,f66,f80,f76,f188])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) != X1
        | v4_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f187])).

fof(f80,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f66,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f227,plain,
    ( spl2_27
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f172,f158,f74,f69,f224])).

fof(f158,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f172,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(unit_resulting_resolution,[],[f71,f76,f159])).

fof(f159,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f213,plain,(
    spl2_25 ),
    inference(avatar_split_clause,[],[f45,f211])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f197,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f44,f195])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f189,plain,(
    spl2_22 ),
    inference(avatar_split_clause,[],[f47,f187])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f180,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f61,f178])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f164,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f46,f162])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f160,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f57,f158])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f148,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f60,f146])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f142,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f125,f106,f74,f139])).

fof(f125,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f76,f107])).

fof(f124,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f55,f122])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f116,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f52,f114])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f112,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f59,f110])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f108,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f58,f106])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f51,f102])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f100,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f50,f98])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f92,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f62,f90])).

fof(f62,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f48,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f86,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f42,f83,f79])).

fof(f42,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f77,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f41,f74])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f40,f69])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f67,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f39,f64])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:00:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.42  % (19979)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (19979)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f1677,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f67,f72,f77,f86,f92,f100,f104,f108,f112,f116,f124,f142,f148,f160,f164,f180,f189,f197,f213,f227,f248,f255,f314,f319,f345,f356,f429,f542,f640,f696,f897,f1117,f1130,f1378,f1582,f1676])).
% 0.21/0.46  fof(f1676,plain,(
% 0.21/0.46    spl2_28 | ~spl2_68 | ~spl2_140),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f1675])).
% 0.21/0.46  fof(f1675,plain,(
% 0.21/0.46    $false | (spl2_28 | ~spl2_68 | ~spl2_140)),
% 0.21/0.46    inference(subsumption_resolution,[],[f247,f1671])).
% 0.21/0.46  fof(f1671,plain,(
% 0.21/0.46    sK1 = k2_pre_topc(sK0,sK1) | (~spl2_68 | ~spl2_140)),
% 0.21/0.46    inference(superposition,[],[f1581,f639])).
% 0.21/0.46  fof(f639,plain,(
% 0.21/0.46    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_68),
% 0.21/0.46    inference(avatar_component_clause,[],[f637])).
% 0.21/0.46  fof(f637,plain,(
% 0.21/0.46    spl2_68 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_68])])).
% 0.21/0.46  fof(f1581,plain,(
% 0.21/0.46    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_140),
% 0.21/0.46    inference(avatar_component_clause,[],[f1579])).
% 0.21/0.46  fof(f1579,plain,(
% 0.21/0.46    spl2_140 <=> sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_140])])).
% 0.21/0.46  fof(f247,plain,(
% 0.21/0.46    sK1 != k2_pre_topc(sK0,sK1) | spl2_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f245])).
% 0.21/0.46  fof(f245,plain,(
% 0.21/0.46    spl2_28 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.21/0.46  fof(f1582,plain,(
% 0.21/0.46    spl2_140 | ~spl2_9 | ~spl2_131),
% 0.21/0.46    inference(avatar_split_clause,[],[f1478,f1375,f102,f1579])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    spl2_9 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.46  fof(f1375,plain,(
% 0.21/0.46    spl2_131 <=> k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_131])])).
% 0.21/0.46  fof(f1478,plain,(
% 0.21/0.46    sK1 = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_9 | ~spl2_131)),
% 0.21/0.46    inference(superposition,[],[f103,f1377])).
% 0.21/0.46  fof(f1377,plain,(
% 0.21/0.46    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_131),
% 0.21/0.46    inference(avatar_component_clause,[],[f1375])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl2_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f102])).
% 0.21/0.46  fof(f1378,plain,(
% 0.21/0.46    spl2_131 | ~spl2_120 | ~spl2_121),
% 0.21/0.46    inference(avatar_split_clause,[],[f1183,f1127,f1115,f1375])).
% 0.21/0.46  fof(f1115,plain,(
% 0.21/0.46    spl2_120 <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_120])])).
% 0.21/0.46  fof(f1127,plain,(
% 0.21/0.46    spl2_121 <=> k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).
% 0.21/0.46  fof(f1183,plain,(
% 0.21/0.46    k2_tops_1(sK0,sK1) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_120 | ~spl2_121)),
% 0.21/0.46    inference(superposition,[],[f1129,f1116])).
% 0.21/0.46  fof(f1116,plain,(
% 0.21/0.46    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | ~spl2_120),
% 0.21/0.46    inference(avatar_component_clause,[],[f1115])).
% 0.21/0.46  fof(f1129,plain,(
% 0.21/0.46    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl2_121),
% 0.21/0.46    inference(avatar_component_clause,[],[f1127])).
% 0.21/0.46  fof(f1130,plain,(
% 0.21/0.46    spl2_121 | ~spl2_14 | ~spl2_62),
% 0.21/0.46    inference(avatar_split_clause,[],[f545,f539,f122,f1127])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    spl2_14 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.46  fof(f539,plain,(
% 0.21/0.46    spl2_62 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).
% 0.21/0.46  fof(f545,plain,(
% 0.21/0.46    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_tops_1(sK0,sK1),sK1) | (~spl2_14 | ~spl2_62)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f541,f123])).
% 0.21/0.46  fof(f123,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f122])).
% 0.21/0.46  fof(f541,plain,(
% 0.21/0.46    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_62),
% 0.21/0.46    inference(avatar_component_clause,[],[f539])).
% 0.21/0.46  fof(f1117,plain,(
% 0.21/0.46    spl2_120 | ~spl2_12 | ~spl2_44),
% 0.21/0.46    inference(avatar_split_clause,[],[f359,f354,f114,f1115])).
% 0.21/0.46  fof(f114,plain,(
% 0.21/0.46    spl2_12 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.46  fof(f354,plain,(
% 0.21/0.46    spl2_44 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 0.21/0.46  fof(f359,plain,(
% 0.21/0.46    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl2_12 | ~spl2_44)),
% 0.21/0.46    inference(superposition,[],[f355,f115])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl2_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f114])).
% 0.21/0.46  fof(f355,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl2_44),
% 0.21/0.46    inference(avatar_component_clause,[],[f354])).
% 0.21/0.46  fof(f897,plain,(
% 0.21/0.46    ~spl2_16 | ~spl2_2 | ~spl2_4 | spl2_36 | ~spl2_29 | ~spl2_37 | ~spl2_53),
% 0.21/0.46    inference(avatar_split_clause,[],[f673,f427,f316,f253,f311,f79,f69,f139])).
% 0.21/0.46  fof(f139,plain,(
% 0.21/0.46    spl2_16 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl2_2 <=> l1_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl2_4 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.46  fof(f311,plain,(
% 0.21/0.46    spl2_36 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.21/0.46  fof(f253,plain,(
% 0.21/0.46    spl2_29 <=> ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.46  fof(f316,plain,(
% 0.21/0.46    spl2_37 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.46  fof(f427,plain,(
% 0.21/0.46    spl2_53 <=> ! [X1,X0] : (~v4_pre_topc(X0,X1) | k2_pre_topc(X1,X0) = X0 | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 0.21/0.46  fof(f673,plain,(
% 0.21/0.46    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(sK1,u1_struct_0(sK0)) | (~spl2_29 | ~spl2_37 | ~spl2_53)),
% 0.21/0.46    inference(forward_demodulation,[],[f435,f254])).
% 0.21/0.46  fof(f254,plain,(
% 0.21/0.46    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | ~spl2_29),
% 0.21/0.46    inference(avatar_component_clause,[],[f253])).
% 0.21/0.46  fof(f435,plain,(
% 0.21/0.46    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~r1_tarski(sK1,u1_struct_0(sK0)) | (~spl2_37 | ~spl2_53)),
% 0.21/0.46    inference(superposition,[],[f318,f428])).
% 0.21/0.46  fof(f428,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_pre_topc(X1,X0) = X0 | ~v4_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1))) ) | ~spl2_53),
% 0.21/0.46    inference(avatar_component_clause,[],[f427])).
% 0.21/0.46  fof(f318,plain,(
% 0.21/0.46    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_37),
% 0.21/0.46    inference(avatar_component_clause,[],[f316])).
% 0.21/0.46  fof(f696,plain,(
% 0.21/0.46    ~spl2_4 | ~spl2_29 | ~spl2_36),
% 0.21/0.46    inference(avatar_split_clause,[],[f694,f311,f253,f79])).
% 0.21/0.46  fof(f694,plain,(
% 0.21/0.46    ~v4_pre_topc(sK1,sK0) | (~spl2_29 | ~spl2_36)),
% 0.21/0.46    inference(subsumption_resolution,[],[f672,f313])).
% 0.21/0.46  fof(f313,plain,(
% 0.21/0.46    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_36),
% 0.21/0.46    inference(avatar_component_clause,[],[f311])).
% 0.21/0.46  fof(f672,plain,(
% 0.21/0.46    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0) | ~spl2_29),
% 0.21/0.46    inference(forward_demodulation,[],[f43,f254])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f17])).
% 0.21/0.47  fof(f17,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.21/0.47  fof(f640,plain,(
% 0.21/0.47    spl2_68 | ~spl2_2 | ~spl2_3 | ~spl2_21 | ~spl2_23 | ~spl2_27),
% 0.21/0.47    inference(avatar_split_clause,[],[f243,f224,f195,f178,f74,f69,f637])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    spl2_21 <=> ! [X1,X0,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.47  fof(f195,plain,(
% 0.21/0.47    spl2_23 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.47  fof(f224,plain,(
% 0.21/0.47    spl2_27 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.47  fof(f243,plain,(
% 0.21/0.47    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_21 | ~spl2_23 | ~spl2_27)),
% 0.21/0.47    inference(forward_demodulation,[],[f235,f199])).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_23)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f71,f76,f196])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_23),
% 0.21/0.47    inference(avatar_component_clause,[],[f195])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f74])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f69])).
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_21 | ~spl2_27)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f76,f226,f179])).
% 0.21/0.47  fof(f179,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f178])).
% 0.21/0.47  fof(f226,plain,(
% 0.21/0.47    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f224])).
% 0.21/0.47  fof(f542,plain,(
% 0.21/0.47    spl2_62 | ~spl2_36 | ~spl2_42),
% 0.21/0.47    inference(avatar_split_clause,[],[f536,f343,f311,f539])).
% 0.21/0.47  fof(f343,plain,(
% 0.21/0.47    spl2_42 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.21/0.47  fof(f536,plain,(
% 0.21/0.47    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl2_36 | ~spl2_42)),
% 0.21/0.47    inference(superposition,[],[f344,f313])).
% 0.21/0.47  fof(f344,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_42),
% 0.21/0.47    inference(avatar_component_clause,[],[f343])).
% 0.21/0.47  fof(f429,plain,(
% 0.21/0.47    spl2_53 | ~spl2_11 | ~spl2_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f181,f162,f110,f427])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl2_11 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    spl2_20 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.47  fof(f181,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_pre_topc(X0,X1) | k2_pre_topc(X1,X0) = X0 | ~l1_pre_topc(X1) | ~r1_tarski(X0,u1_struct_0(X1))) ) | (~spl2_11 | ~spl2_20)),
% 0.21/0.47    inference(resolution,[],[f163,f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) ) | ~spl2_20),
% 0.21/0.47    inference(avatar_component_clause,[],[f162])).
% 0.21/0.47  fof(f356,plain,(
% 0.21/0.47    spl2_44 | ~spl2_8 | ~spl2_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f134,f114,f98,f354])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl2_8 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl2_8 | ~spl2_12)),
% 0.21/0.47    inference(superposition,[],[f115,f99])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f98])).
% 0.21/0.47  fof(f345,plain,(
% 0.21/0.47    spl2_42 | ~spl2_6 | ~spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f126,f106,f90,f343])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl2_6 <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    spl2_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | (~spl2_6 | ~spl2_10)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f91,f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f106])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f90])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    spl2_37 | ~spl2_2 | ~spl2_3 | ~spl2_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f214,f211,f74,f69,f316])).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    spl2_25 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.47  fof(f214,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_25)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f71,f76,f212])).
% 0.21/0.47  fof(f212,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_25),
% 0.21/0.47    inference(avatar_component_clause,[],[f211])).
% 0.21/0.47  fof(f314,plain,(
% 0.21/0.47    ~spl2_3 | spl2_36 | ~spl2_5 | ~spl2_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f151,f146,f83,f311,f74])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    spl2_17 <=> ! [X1,X0,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | ~spl2_17)),
% 0.21/0.47    inference(superposition,[],[f147,f85])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f83])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f146])).
% 0.21/0.47  fof(f255,plain,(
% 0.21/0.47    spl2_29 | ~spl2_3 | ~spl2_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f149,f146,f74,f253])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) ) | (~spl2_3 | ~spl2_17)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f76,f147])).
% 0.21/0.47  fof(f248,plain,(
% 0.21/0.47    ~spl2_28 | ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f198,f187,f79,f74,f69,f64,f245])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl2_1 <=> v2_pre_topc(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f187,plain,(
% 0.21/0.47    spl2_22 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    sK1 != k2_pre_topc(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_22)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f71,f66,f80,f76,f188])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f187])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ~v4_pre_topc(sK1,sK0) | spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f79])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    v2_pre_topc(sK0) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f64])).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    spl2_27 | ~spl2_2 | ~spl2_3 | ~spl2_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f172,f158,f74,f69,f224])).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    spl2_19 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3 | ~spl2_19)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f71,f76,f159])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f158])).
% 0.21/0.47  fof(f213,plain,(
% 0.21/0.47    spl2_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f45,f211])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.21/0.47  fof(f197,plain,(
% 0.21/0.47    spl2_23),
% 0.21/0.47    inference(avatar_split_clause,[],[f44,f195])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    spl2_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f47,f187])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    spl2_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f61,f178])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(flattening,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    spl2_20),
% 0.21/0.47    inference(avatar_split_clause,[],[f46,f162])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    spl2_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f57,f158])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    spl2_17),
% 0.21/0.47    inference(avatar_split_clause,[],[f60,f146])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    spl2_16 | ~spl2_3 | ~spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f125,f106,f74,f139])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    r1_tarski(sK1,u1_struct_0(sK0)) | (~spl2_3 | ~spl2_10)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f76,f107])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    spl2_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f55,f122])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    spl2_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f52,f114])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl2_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f59,f110])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.47    inference(nnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    spl2_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f58,f106])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f38])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl2_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f51,f102])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl2_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f50,f98])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl2_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f62,f90])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(forward_demodulation,[],[f48,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl2_4 | spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f42,f83,f79])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl2_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f74])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f69])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl2_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f64])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (19979)------------------------------
% 0.21/0.47  % (19979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19979)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (19979)Memory used [KB]: 7675
% 0.21/0.47  % (19979)Time elapsed: 0.052 s
% 0.21/0.47  % (19979)------------------------------
% 0.21/0.47  % (19979)------------------------------
% 0.21/0.47  % (19970)Success in time 0.109 s
%------------------------------------------------------------------------------
