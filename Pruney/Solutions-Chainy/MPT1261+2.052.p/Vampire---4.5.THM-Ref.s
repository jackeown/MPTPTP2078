%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:55 EST 2020

% Result     : Theorem 3.51s
% Output     : Refutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 374 expanded)
%              Number of leaves         :   39 ( 136 expanded)
%              Depth                    :   15
%              Number of atoms          :  434 (1042 expanded)
%              Number of equality atoms :  102 ( 324 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7530,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f114,f510,f1489,f1727,f2118,f2123,f2430,f2765,f2821,f2824,f2833,f2835,f3802,f5413,f7454,f7529])).

fof(f7529,plain,
    ( ~ spl2_9
    | spl2_52 ),
    inference(avatar_contradiction_clause,[],[f7525])).

fof(f7525,plain,
    ( $false
    | ~ spl2_9
    | spl2_52 ),
    inference(resolution,[],[f7524,f506])).

fof(f506,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f504])).

fof(f504,plain,
    ( spl2_9
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f7524,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_52 ),
    inference(resolution,[],[f2156,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2156,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_52 ),
    inference(avatar_component_clause,[],[f2155])).

fof(f2155,plain,
    ( spl2_52
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f7454,plain,
    ( ~ spl2_52
    | ~ spl2_32
    | ~ spl2_8
    | spl2_51 ),
    inference(avatar_split_clause,[],[f7451,f2150,f500,f1480,f2155])).

fof(f1480,plain,
    ( spl2_32
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f500,plain,
    ( spl2_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f2150,plain,
    ( spl2_51
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).

fof(f7451,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_51 ),
    inference(trivial_inequality_removal,[],[f7450])).

fof(f7450,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_51 ),
    inference(superposition,[],[f2151,f1069])).

fof(f1069,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1058])).

fof(f1058,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(X1)) ) ),
    inference(superposition,[],[f68,f362])).

fof(f362,plain,(
    ! [X8,X7,X9] :
      ( k3_subset_1(X7,X8) = k7_subset_1(X9,X7,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X9))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X7)) ) ),
    inference(superposition,[],[f101,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f79,f91])).

fof(f91,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f76,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f86,f91])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f2151,plain,
    ( k1_tops_1(sK0,sK1) != k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | spl2_51 ),
    inference(avatar_component_clause,[],[f2150])).

fof(f5413,plain,
    ( ~ spl2_20
    | ~ spl2_8
    | ~ spl2_21
    | spl2_2 ),
    inference(avatar_split_clause,[],[f5408,f110,f1079,f500,f1075])).

fof(f1075,plain,
    ( spl2_20
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f1079,plain,
    ( spl2_21
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f110,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f5408,plain,
    ( k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_2 ),
    inference(superposition,[],[f112,f362])).

fof(f112,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f3802,plain,
    ( ~ spl2_52
    | spl2_21
    | ~ spl2_51 ),
    inference(avatar_split_clause,[],[f3789,f2150,f1079,f2155])).

fof(f3789,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl2_51 ),
    inference(superposition,[],[f80,f2152])).

fof(f2152,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_51 ),
    inference(avatar_component_clause,[],[f2150])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2835,plain,(
    spl2_76 ),
    inference(avatar_contradiction_clause,[],[f2834])).

fof(f2834,plain,
    ( $false
    | spl2_76 ),
    inference(resolution,[],[f2832,f58])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).

fof(f54,plain,
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

fof(f55,plain,
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

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f2832,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_76 ),
    inference(avatar_component_clause,[],[f2830])).

fof(f2830,plain,
    ( spl2_76
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).

fof(f2833,plain,
    ( ~ spl2_76
    | ~ spl2_32
    | ~ spl2_8
    | spl2_1
    | ~ spl2_65 ),
    inference(avatar_split_clause,[],[f2828,f2393,f106,f500,f1480,f2830])).

fof(f106,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f2393,plain,
    ( spl2_65
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f2828,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_65 ),
    inference(superposition,[],[f82,f2395])).

fof(f2395,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f2393])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f2824,plain,
    ( ~ spl2_32
    | ~ spl2_8
    | spl2_75 ),
    inference(avatar_split_clause,[],[f2822,f2817,f500,f1480])).

fof(f2817,plain,
    ( spl2_75
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f2822,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_75 ),
    inference(resolution,[],[f2819,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f2819,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_75 ),
    inference(avatar_component_clause,[],[f2817])).

fof(f2821,plain,
    ( ~ spl2_32
    | ~ spl2_8
    | ~ spl2_75
    | spl2_65
    | ~ spl2_44 ),
    inference(avatar_split_clause,[],[f2809,f1935,f2393,f2817,f500,f1480])).

fof(f1935,plain,
    ( spl2_44
  <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f2809,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_44 ),
    inference(superposition,[],[f451,f1937])).

fof(f1937,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f1935])).

fof(f451,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f450])).

fof(f450,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f104,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f90,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f2765,plain,
    ( ~ spl2_9
    | spl2_44 ),
    inference(avatar_contradiction_clause,[],[f2760])).

fof(f2760,plain,
    ( $false
    | ~ spl2_9
    | spl2_44 ),
    inference(resolution,[],[f2749,f506])).

fof(f2749,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_44 ),
    inference(trivial_inequality_removal,[],[f2748])).

fof(f2748,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_44 ),
    inference(superposition,[],[f1936,f388])).

fof(f388,plain,(
    ! [X23,X22] :
      ( k3_tarski(k2_tarski(X23,X22)) = X23
      | ~ r1_tarski(X22,X23) ) ),
    inference(superposition,[],[f146,f354])).

fof(f354,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(k2_tarski(X2,X3)) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f345,f93])).

fof(f93,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f64,f75])).

fof(f64,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f345,plain,(
    ! [X2,X3] :
      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X2,X3)),k1_xboole_0)) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f98,f288])).

fof(f288,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 = k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7)))
      | ~ r1_tarski(X6,X7) ) ),
    inference(forward_demodulation,[],[f281,f93])).

fof(f281,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k3_tarski(k2_tarski(X7,k1_xboole_0)))
      | k1_xboole_0 = k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7))) ) ),
    inference(resolution,[],[f102,f178])).

fof(f178,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f177,f133])).

fof(f133,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f94,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f63,f74])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f94,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f65,f91])).

fof(f65,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f177,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f100,f117])).

fof(f117,plain,(
    ! [X1] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1)) ),
    inference(superposition,[],[f92,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f81,f91])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2)
      | ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f87,f91,f75])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f98,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f77,f75,f74,f91])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f146,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0 ),
    inference(superposition,[],[f97,f72])).

fof(f97,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f73,f75,f74])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1936,plain,
    ( sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | spl2_44 ),
    inference(avatar_component_clause,[],[f1935])).

fof(f2430,plain,
    ( ~ spl2_8
    | spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f2420,f110,f504,f500])).

fof(f2420,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f363,f111])).

fof(f111,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f363,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_subset_1(X2,X0,X1),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f96,f101])).

fof(f96,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f71,f91])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2123,plain,
    ( spl2_20
    | ~ spl2_48 ),
    inference(avatar_contradiction_clause,[],[f2119])).

fof(f2119,plain,
    ( $false
    | spl2_20
    | ~ spl2_48 ),
    inference(resolution,[],[f2117,f1084])).

fof(f1084,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | spl2_20 ),
    inference(resolution,[],[f1077,f85])).

fof(f1077,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | spl2_20 ),
    inference(avatar_component_clause,[],[f1075])).

fof(f2117,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_48 ),
    inference(avatar_component_clause,[],[f2115])).

fof(f2115,plain,
    ( spl2_48
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).

fof(f2118,plain,
    ( ~ spl2_32
    | spl2_48 ),
    inference(avatar_split_clause,[],[f2112,f2115,f1480])).

fof(f2112,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f498,f60])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f498,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f495])).

fof(f495,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f363,f68])).

fof(f1727,plain,
    ( ~ spl2_32
    | spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f326,f106,f504,f1480])).

fof(f326,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f69,f60])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f1489,plain,(
    spl2_32 ),
    inference(avatar_contradiction_clause,[],[f1488])).

fof(f1488,plain,
    ( $false
    | spl2_32 ),
    inference(resolution,[],[f1482,f59])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f1482,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_32 ),
    inference(avatar_component_clause,[],[f1480])).

fof(f510,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f502,f60])).

fof(f502,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f500])).

fof(f114,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f61,f110,f106])).

fof(f61,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f113,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f62,f110,f106])).

fof(f62,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:36:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.42  % (29164)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.45  % (29163)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.45  % (29156)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.45  % (29160)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.45  % (29151)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (29152)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (29155)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (29161)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (29149)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (29150)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (29153)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (29159)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (29157)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (29158)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (29166)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (29162)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (29154)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (29165)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 3.51/0.80  % (29153)Refutation found. Thanks to Tanya!
% 3.51/0.80  % SZS status Theorem for theBenchmark
% 3.51/0.80  % SZS output start Proof for theBenchmark
% 3.51/0.80  fof(f7530,plain,(
% 3.51/0.80    $false),
% 3.51/0.80    inference(avatar_sat_refutation,[],[f113,f114,f510,f1489,f1727,f2118,f2123,f2430,f2765,f2821,f2824,f2833,f2835,f3802,f5413,f7454,f7529])).
% 3.51/0.80  fof(f7529,plain,(
% 3.51/0.80    ~spl2_9 | spl2_52),
% 3.51/0.80    inference(avatar_contradiction_clause,[],[f7525])).
% 3.51/0.80  fof(f7525,plain,(
% 3.51/0.80    $false | (~spl2_9 | spl2_52)),
% 3.51/0.80    inference(resolution,[],[f7524,f506])).
% 3.51/0.80  fof(f506,plain,(
% 3.51/0.80    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_9),
% 3.51/0.80    inference(avatar_component_clause,[],[f504])).
% 3.51/0.80  fof(f504,plain,(
% 3.51/0.80    spl2_9 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.51/0.80  fof(f7524,plain,(
% 3.51/0.80    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_52),
% 3.51/0.80    inference(resolution,[],[f2156,f85])).
% 3.51/0.80  fof(f85,plain,(
% 3.51/0.80    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.51/0.80    inference(cnf_transformation,[],[f57])).
% 3.51/0.80  fof(f57,plain,(
% 3.51/0.80    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.51/0.80    inference(nnf_transformation,[],[f21])).
% 3.51/0.80  fof(f21,axiom,(
% 3.51/0.80    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.51/0.80  fof(f2156,plain,(
% 3.51/0.80    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_52),
% 3.51/0.80    inference(avatar_component_clause,[],[f2155])).
% 3.51/0.80  fof(f2155,plain,(
% 3.51/0.80    spl2_52 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 3.51/0.80  fof(f7454,plain,(
% 3.51/0.80    ~spl2_52 | ~spl2_32 | ~spl2_8 | spl2_51),
% 3.51/0.80    inference(avatar_split_clause,[],[f7451,f2150,f500,f1480,f2155])).
% 3.51/0.80  fof(f1480,plain,(
% 3.51/0.80    spl2_32 <=> l1_pre_topc(sK0)),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 3.51/0.80  fof(f500,plain,(
% 3.51/0.80    spl2_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 3.51/0.80  fof(f2150,plain,(
% 3.51/0.80    spl2_51 <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_51])])).
% 3.51/0.80  fof(f7451,plain,(
% 3.51/0.80    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_51),
% 3.51/0.80    inference(trivial_inequality_removal,[],[f7450])).
% 3.51/0.80  fof(f7450,plain,(
% 3.51/0.80    k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_51),
% 3.51/0.80    inference(superposition,[],[f2151,f1069])).
% 3.51/0.80  fof(f1069,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(X1))) )),
% 3.51/0.80    inference(duplicate_literal_removal,[],[f1058])).
% 3.51/0.80  fof(f1058,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(X1))) )),
% 3.51/0.80    inference(superposition,[],[f68,f362])).
% 3.51/0.80  fof(f362,plain,(
% 3.51/0.80    ( ! [X8,X7,X9] : (k3_subset_1(X7,X8) = k7_subset_1(X9,X7,X8) | ~m1_subset_1(X7,k1_zfmisc_1(X9)) | ~m1_subset_1(X8,k1_zfmisc_1(X7))) )),
% 3.51/0.80    inference(superposition,[],[f101,f99])).
% 3.51/0.80  fof(f99,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.80    inference(definition_unfolding,[],[f79,f91])).
% 3.51/0.80  fof(f91,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.51/0.80    inference(definition_unfolding,[],[f76,f74])).
% 3.51/0.80  fof(f74,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.51/0.80    inference(cnf_transformation,[],[f20])).
% 3.51/0.80  fof(f20,axiom,(
% 3.51/0.80    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.51/0.80  fof(f76,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.51/0.80    inference(cnf_transformation,[],[f1])).
% 3.51/0.80  fof(f1,axiom,(
% 3.51/0.80    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.51/0.80  fof(f79,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.80    inference(cnf_transformation,[],[f38])).
% 3.51/0.80  fof(f38,plain,(
% 3.51/0.80    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.80    inference(ennf_transformation,[],[f15])).
% 3.51/0.80  fof(f15,axiom,(
% 3.51/0.80    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.51/0.80  fof(f101,plain,(
% 3.51/0.80    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.80    inference(definition_unfolding,[],[f86,f91])).
% 3.51/0.80  fof(f86,plain,(
% 3.51/0.80    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.80    inference(cnf_transformation,[],[f45])).
% 3.51/0.80  fof(f45,plain,(
% 3.51/0.80    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.80    inference(ennf_transformation,[],[f19])).
% 3.51/0.80  fof(f19,axiom,(
% 3.51/0.80    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.51/0.80  fof(f68,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.80    inference(cnf_transformation,[],[f34])).
% 3.51/0.80  fof(f34,plain,(
% 3.51/0.80    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.80    inference(ennf_transformation,[],[f27])).
% 3.51/0.80  fof(f27,axiom,(
% 3.51/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 3.51/0.80  fof(f2151,plain,(
% 3.51/0.80    k1_tops_1(sK0,sK1) != k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | spl2_51),
% 3.51/0.80    inference(avatar_component_clause,[],[f2150])).
% 3.51/0.80  fof(f5413,plain,(
% 3.51/0.80    ~spl2_20 | ~spl2_8 | ~spl2_21 | spl2_2),
% 3.51/0.80    inference(avatar_split_clause,[],[f5408,f110,f1079,f500,f1075])).
% 3.51/0.80  fof(f1075,plain,(
% 3.51/0.80    spl2_20 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 3.51/0.80  fof(f1079,plain,(
% 3.51/0.80    spl2_21 <=> k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 3.51/0.80  fof(f110,plain,(
% 3.51/0.80    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.51/0.80  fof(f5408,plain,(
% 3.51/0.80    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_2),
% 3.51/0.80    inference(superposition,[],[f112,f362])).
% 3.51/0.80  fof(f112,plain,(
% 3.51/0.80    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl2_2),
% 3.51/0.80    inference(avatar_component_clause,[],[f110])).
% 3.51/0.80  fof(f3802,plain,(
% 3.51/0.80    ~spl2_52 | spl2_21 | ~spl2_51),
% 3.51/0.80    inference(avatar_split_clause,[],[f3789,f2150,f1079,f2155])).
% 3.51/0.80  fof(f3789,plain,(
% 3.51/0.80    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl2_51),
% 3.51/0.80    inference(superposition,[],[f80,f2152])).
% 3.51/0.80  fof(f2152,plain,(
% 3.51/0.80    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl2_51),
% 3.51/0.80    inference(avatar_component_clause,[],[f2150])).
% 3.51/0.80  fof(f80,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.80    inference(cnf_transformation,[],[f39])).
% 3.51/0.80  fof(f39,plain,(
% 3.51/0.80    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.80    inference(ennf_transformation,[],[f17])).
% 3.51/0.80  fof(f17,axiom,(
% 3.51/0.80    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.51/0.80  fof(f2835,plain,(
% 3.51/0.80    spl2_76),
% 3.51/0.80    inference(avatar_contradiction_clause,[],[f2834])).
% 3.51/0.80  fof(f2834,plain,(
% 3.51/0.80    $false | spl2_76),
% 3.51/0.80    inference(resolution,[],[f2832,f58])).
% 3.51/0.80  fof(f58,plain,(
% 3.51/0.80    v2_pre_topc(sK0)),
% 3.51/0.80    inference(cnf_transformation,[],[f56])).
% 3.51/0.80  fof(f56,plain,(
% 3.51/0.80    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.51/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).
% 3.51/0.80  fof(f54,plain,(
% 3.51/0.80    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.51/0.80    introduced(choice_axiom,[])).
% 3.51/0.80  fof(f55,plain,(
% 3.51/0.80    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.51/0.80    introduced(choice_axiom,[])).
% 3.51/0.80  fof(f53,plain,(
% 3.51/0.80    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.51/0.80    inference(flattening,[],[f52])).
% 3.51/0.80  fof(f52,plain,(
% 3.51/0.80    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.51/0.80    inference(nnf_transformation,[],[f31])).
% 3.51/0.80  fof(f31,plain,(
% 3.51/0.80    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.51/0.80    inference(flattening,[],[f30])).
% 3.51/0.80  fof(f30,plain,(
% 3.51/0.80    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.51/0.80    inference(ennf_transformation,[],[f29])).
% 3.51/0.80  fof(f29,negated_conjecture,(
% 3.51/0.80    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.51/0.80    inference(negated_conjecture,[],[f28])).
% 3.51/0.80  fof(f28,conjecture,(
% 3.51/0.80    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 3.51/0.80  fof(f2832,plain,(
% 3.51/0.80    ~v2_pre_topc(sK0) | spl2_76),
% 3.51/0.80    inference(avatar_component_clause,[],[f2830])).
% 3.51/0.80  fof(f2830,plain,(
% 3.51/0.80    spl2_76 <=> v2_pre_topc(sK0)),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_76])])).
% 3.51/0.80  fof(f2833,plain,(
% 3.51/0.80    ~spl2_76 | ~spl2_32 | ~spl2_8 | spl2_1 | ~spl2_65),
% 3.51/0.80    inference(avatar_split_clause,[],[f2828,f2393,f106,f500,f1480,f2830])).
% 3.51/0.80  fof(f106,plain,(
% 3.51/0.80    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.51/0.80  fof(f2393,plain,(
% 3.51/0.80    spl2_65 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 3.51/0.80  fof(f2828,plain,(
% 3.51/0.80    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_65),
% 3.51/0.80    inference(superposition,[],[f82,f2395])).
% 3.51/0.80  fof(f2395,plain,(
% 3.51/0.80    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_65),
% 3.51/0.80    inference(avatar_component_clause,[],[f2393])).
% 3.51/0.80  fof(f82,plain,(
% 3.51/0.80    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.51/0.80    inference(cnf_transformation,[],[f42])).
% 3.51/0.80  fof(f42,plain,(
% 3.51/0.80    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.51/0.80    inference(flattening,[],[f41])).
% 3.51/0.80  fof(f41,plain,(
% 3.51/0.80    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.51/0.80    inference(ennf_transformation,[],[f23])).
% 3.51/0.80  fof(f23,axiom,(
% 3.51/0.80    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 3.51/0.80  fof(f2824,plain,(
% 3.51/0.80    ~spl2_32 | ~spl2_8 | spl2_75),
% 3.51/0.80    inference(avatar_split_clause,[],[f2822,f2817,f500,f1480])).
% 3.51/0.80  fof(f2817,plain,(
% 3.51/0.80    spl2_75 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 3.51/0.80  fof(f2822,plain,(
% 3.51/0.80    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_75),
% 3.51/0.80    inference(resolution,[],[f2819,f83])).
% 3.51/0.80  fof(f83,plain,(
% 3.51/0.80    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.80    inference(cnf_transformation,[],[f44])).
% 3.51/0.80  fof(f44,plain,(
% 3.51/0.80    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.51/0.80    inference(flattening,[],[f43])).
% 3.51/0.80  fof(f43,plain,(
% 3.51/0.80    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.51/0.80    inference(ennf_transformation,[],[f22])).
% 3.51/0.80  fof(f22,axiom,(
% 3.51/0.80    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.51/0.80  fof(f2819,plain,(
% 3.51/0.80    ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_75),
% 3.51/0.80    inference(avatar_component_clause,[],[f2817])).
% 3.51/0.80  fof(f2821,plain,(
% 3.51/0.80    ~spl2_32 | ~spl2_8 | ~spl2_75 | spl2_65 | ~spl2_44),
% 3.51/0.80    inference(avatar_split_clause,[],[f2809,f1935,f2393,f2817,f500,f1480])).
% 3.51/0.80  fof(f1935,plain,(
% 3.51/0.80    spl2_44 <=> sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 3.51/0.80  fof(f2809,plain,(
% 3.51/0.80    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_44),
% 3.51/0.80    inference(superposition,[],[f451,f1937])).
% 3.51/0.80  fof(f1937,plain,(
% 3.51/0.80    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | ~spl2_44),
% 3.51/0.80    inference(avatar_component_clause,[],[f1935])).
% 3.51/0.80  fof(f451,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.80    inference(duplicate_literal_removal,[],[f450])).
% 3.51/0.80  fof(f450,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.80    inference(superposition,[],[f104,f67])).
% 3.51/0.80  fof(f67,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.80    inference(cnf_transformation,[],[f33])).
% 3.51/0.80  fof(f33,plain,(
% 3.51/0.80    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.80    inference(ennf_transformation,[],[f25])).
% 3.51/0.80  fof(f25,axiom,(
% 3.51/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.51/0.80  fof(f104,plain,(
% 3.51/0.80    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.80    inference(definition_unfolding,[],[f90,f75])).
% 3.51/0.80  fof(f75,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.51/0.80    inference(cnf_transformation,[],[f14])).
% 3.51/0.80  fof(f14,axiom,(
% 3.51/0.80    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.51/0.80  fof(f90,plain,(
% 3.51/0.80    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.51/0.80    inference(cnf_transformation,[],[f51])).
% 3.51/0.80  fof(f51,plain,(
% 3.51/0.80    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.51/0.80    inference(flattening,[],[f50])).
% 3.51/0.80  fof(f50,plain,(
% 3.51/0.80    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.51/0.80    inference(ennf_transformation,[],[f18])).
% 3.51/0.80  fof(f18,axiom,(
% 3.51/0.80    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.51/0.80  fof(f2765,plain,(
% 3.51/0.80    ~spl2_9 | spl2_44),
% 3.51/0.80    inference(avatar_contradiction_clause,[],[f2760])).
% 3.51/0.80  fof(f2760,plain,(
% 3.51/0.80    $false | (~spl2_9 | spl2_44)),
% 3.51/0.80    inference(resolution,[],[f2749,f506])).
% 3.51/0.80  fof(f2749,plain,(
% 3.51/0.80    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_44),
% 3.51/0.80    inference(trivial_inequality_removal,[],[f2748])).
% 3.51/0.80  fof(f2748,plain,(
% 3.51/0.80    sK1 != sK1 | ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_44),
% 3.51/0.80    inference(superposition,[],[f1936,f388])).
% 3.51/0.80  fof(f388,plain,(
% 3.51/0.80    ( ! [X23,X22] : (k3_tarski(k2_tarski(X23,X22)) = X23 | ~r1_tarski(X22,X23)) )),
% 3.51/0.80    inference(superposition,[],[f146,f354])).
% 3.51/0.80  fof(f354,plain,(
% 3.51/0.80    ( ! [X2,X3] : (k1_setfam_1(k2_tarski(X2,X3)) = X2 | ~r1_tarski(X2,X3)) )),
% 3.51/0.80    inference(forward_demodulation,[],[f345,f93])).
% 3.51/0.80  fof(f93,plain,(
% 3.51/0.80    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 3.51/0.80    inference(definition_unfolding,[],[f64,f75])).
% 3.51/0.80  fof(f64,plain,(
% 3.51/0.80    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.51/0.80    inference(cnf_transformation,[],[f2])).
% 3.51/0.80  fof(f2,axiom,(
% 3.51/0.80    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 3.51/0.80  fof(f345,plain,(
% 3.51/0.80    ( ! [X2,X3] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X2,X3)),k1_xboole_0)) = X2 | ~r1_tarski(X2,X3)) )),
% 3.51/0.80    inference(superposition,[],[f98,f288])).
% 3.51/0.80  fof(f288,plain,(
% 3.51/0.80    ( ! [X6,X7] : (k1_xboole_0 = k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7))) | ~r1_tarski(X6,X7)) )),
% 3.51/0.80    inference(forward_demodulation,[],[f281,f93])).
% 3.51/0.80  fof(f281,plain,(
% 3.51/0.80    ( ! [X6,X7] : (~r1_tarski(X6,k3_tarski(k2_tarski(X7,k1_xboole_0))) | k1_xboole_0 = k5_xboole_0(X6,k1_setfam_1(k2_tarski(X6,X7)))) )),
% 3.51/0.80    inference(resolution,[],[f102,f178])).
% 3.51/0.80  fof(f178,plain,(
% 3.51/0.80    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 3.51/0.80    inference(forward_demodulation,[],[f177,f133])).
% 3.51/0.80  fof(f133,plain,(
% 3.51/0.80    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.51/0.80    inference(forward_demodulation,[],[f94,f92])).
% 3.51/0.80  fof(f92,plain,(
% 3.51/0.80    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 3.51/0.80    inference(definition_unfolding,[],[f63,f74])).
% 3.51/0.80  fof(f63,plain,(
% 3.51/0.80    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.51/0.80    inference(cnf_transformation,[],[f5])).
% 3.51/0.80  fof(f5,axiom,(
% 3.51/0.80    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 3.51/0.80  fof(f94,plain,(
% 3.51/0.80    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 3.51/0.80    inference(definition_unfolding,[],[f65,f91])).
% 3.51/0.80  fof(f65,plain,(
% 3.51/0.80    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.51/0.80    inference(cnf_transformation,[],[f8])).
% 3.51/0.80  fof(f8,axiom,(
% 3.51/0.80    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.51/0.80  fof(f177,plain,(
% 3.51/0.80    ( ! [X1] : (~r1_tarski(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = X1) )),
% 3.51/0.80    inference(superposition,[],[f100,f117])).
% 3.51/0.80  fof(f117,plain,(
% 3.51/0.80    ( ! [X1] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X1))) )),
% 3.51/0.80    inference(superposition,[],[f92,f72])).
% 3.51/0.80  fof(f72,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.51/0.80    inference(cnf_transformation,[],[f13])).
% 3.51/0.80  fof(f13,axiom,(
% 3.51/0.80    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.51/0.80  fof(f100,plain,(
% 3.51/0.80    ( ! [X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) | k1_xboole_0 = X0) )),
% 3.51/0.80    inference(definition_unfolding,[],[f81,f91])).
% 3.51/0.80  fof(f81,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 3.51/0.80    inference(cnf_transformation,[],[f40])).
% 3.51/0.80  fof(f40,plain,(
% 3.51/0.80    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 3.51/0.80    inference(ennf_transformation,[],[f7])).
% 3.51/0.80  fof(f7,axiom,(
% 3.51/0.80    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 3.51/0.80  fof(f102,plain,(
% 3.51/0.80    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X2) | ~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))) )),
% 3.51/0.80    inference(definition_unfolding,[],[f87,f91,f75])).
% 3.51/0.80  fof(f87,plain,(
% 3.51/0.80    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.51/0.80    inference(cnf_transformation,[],[f46])).
% 3.51/0.80  fof(f46,plain,(
% 3.51/0.80    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.51/0.80    inference(ennf_transformation,[],[f9])).
% 3.51/0.80  fof(f9,axiom,(
% 3.51/0.80    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.51/0.80  fof(f98,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))) = X0) )),
% 3.51/0.80    inference(definition_unfolding,[],[f77,f75,f74,f91])).
% 3.51/0.80  fof(f77,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.51/0.80    inference(cnf_transformation,[],[f11])).
% 3.51/0.80  fof(f11,axiom,(
% 3.51/0.80    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 3.51/0.80  fof(f146,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X1,X0)))) = X0) )),
% 3.51/0.80    inference(superposition,[],[f97,f72])).
% 3.51/0.80  fof(f97,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 3.51/0.80    inference(definition_unfolding,[],[f73,f75,f74])).
% 3.51/0.80  fof(f73,plain,(
% 3.51/0.80    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.51/0.80    inference(cnf_transformation,[],[f4])).
% 3.51/0.80  fof(f4,axiom,(
% 3.51/0.80    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 3.51/0.80  fof(f1936,plain,(
% 3.51/0.80    sK1 != k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | spl2_44),
% 3.51/0.80    inference(avatar_component_clause,[],[f1935])).
% 3.51/0.80  fof(f2430,plain,(
% 3.51/0.80    ~spl2_8 | spl2_9 | ~spl2_2),
% 3.51/0.80    inference(avatar_split_clause,[],[f2420,f110,f504,f500])).
% 3.51/0.80  fof(f2420,plain,(
% 3.51/0.80    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 3.51/0.80    inference(superposition,[],[f363,f111])).
% 3.51/0.80  fof(f111,plain,(
% 3.51/0.80    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 3.51/0.80    inference(avatar_component_clause,[],[f110])).
% 3.51/0.80  fof(f363,plain,(
% 3.51/0.80    ( ! [X2,X0,X1] : (r1_tarski(k7_subset_1(X2,X0,X1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2))) )),
% 3.51/0.80    inference(superposition,[],[f96,f101])).
% 3.51/0.80  fof(f96,plain,(
% 3.51/0.80    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 3.51/0.80    inference(definition_unfolding,[],[f71,f91])).
% 3.51/0.80  fof(f71,plain,(
% 3.51/0.80    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.51/0.80    inference(cnf_transformation,[],[f6])).
% 3.51/0.80  fof(f6,axiom,(
% 3.51/0.80    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.51/0.80  fof(f2123,plain,(
% 3.51/0.80    spl2_20 | ~spl2_48),
% 3.51/0.80    inference(avatar_contradiction_clause,[],[f2119])).
% 3.51/0.80  fof(f2119,plain,(
% 3.51/0.80    $false | (spl2_20 | ~spl2_48)),
% 3.51/0.80    inference(resolution,[],[f2117,f1084])).
% 3.51/0.80  fof(f1084,plain,(
% 3.51/0.80    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | spl2_20),
% 3.51/0.80    inference(resolution,[],[f1077,f85])).
% 3.51/0.80  fof(f1077,plain,(
% 3.51/0.80    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | spl2_20),
% 3.51/0.80    inference(avatar_component_clause,[],[f1075])).
% 3.51/0.80  fof(f2117,plain,(
% 3.51/0.80    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_48),
% 3.51/0.80    inference(avatar_component_clause,[],[f2115])).
% 3.51/0.80  fof(f2115,plain,(
% 3.51/0.80    spl2_48 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.51/0.80    introduced(avatar_definition,[new_symbols(naming,[spl2_48])])).
% 3.51/0.80  fof(f2118,plain,(
% 3.51/0.80    ~spl2_32 | spl2_48),
% 3.51/0.80    inference(avatar_split_clause,[],[f2112,f2115,f1480])).
% 3.51/0.80  fof(f2112,plain,(
% 3.51/0.80    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 3.51/0.80    inference(resolution,[],[f498,f60])).
% 3.51/0.80  fof(f60,plain,(
% 3.51/0.80    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.51/0.80    inference(cnf_transformation,[],[f56])).
% 3.51/0.80  fof(f498,plain,(
% 3.51/0.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 3.51/0.80    inference(duplicate_literal_removal,[],[f495])).
% 3.51/0.80  fof(f495,plain,(
% 3.51/0.80    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.51/0.80    inference(superposition,[],[f363,f68])).
% 3.51/0.80  fof(f1727,plain,(
% 3.51/0.80    ~spl2_32 | spl2_9 | ~spl2_1),
% 3.51/0.80    inference(avatar_split_clause,[],[f326,f106,f504,f1480])).
% 3.51/0.80  fof(f326,plain,(
% 3.51/0.80    ~v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 3.51/0.80    inference(resolution,[],[f69,f60])).
% 3.51/0.80  fof(f69,plain,(
% 3.51/0.80    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 3.51/0.80    inference(cnf_transformation,[],[f36])).
% 3.51/0.80  fof(f36,plain,(
% 3.51/0.80    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.80    inference(flattening,[],[f35])).
% 3.51/0.80  fof(f35,plain,(
% 3.51/0.80    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.51/0.80    inference(ennf_transformation,[],[f26])).
% 3.51/0.80  fof(f26,axiom,(
% 3.51/0.80    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 3.51/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 3.51/0.80  fof(f1489,plain,(
% 3.51/0.80    spl2_32),
% 3.51/0.80    inference(avatar_contradiction_clause,[],[f1488])).
% 3.51/0.80  fof(f1488,plain,(
% 3.51/0.80    $false | spl2_32),
% 3.51/0.80    inference(resolution,[],[f1482,f59])).
% 3.51/0.80  fof(f59,plain,(
% 3.51/0.80    l1_pre_topc(sK0)),
% 3.51/0.80    inference(cnf_transformation,[],[f56])).
% 3.51/0.80  fof(f1482,plain,(
% 3.51/0.80    ~l1_pre_topc(sK0) | spl2_32),
% 3.51/0.80    inference(avatar_component_clause,[],[f1480])).
% 3.51/0.80  fof(f510,plain,(
% 3.51/0.80    spl2_8),
% 3.51/0.80    inference(avatar_contradiction_clause,[],[f508])).
% 3.51/0.80  fof(f508,plain,(
% 3.51/0.80    $false | spl2_8),
% 3.51/0.80    inference(resolution,[],[f502,f60])).
% 3.51/0.80  fof(f502,plain,(
% 3.51/0.80    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_8),
% 3.51/0.80    inference(avatar_component_clause,[],[f500])).
% 3.51/0.80  fof(f114,plain,(
% 3.51/0.80    spl2_1 | spl2_2),
% 3.51/0.80    inference(avatar_split_clause,[],[f61,f110,f106])).
% 3.51/0.80  fof(f61,plain,(
% 3.51/0.80    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 3.51/0.80    inference(cnf_transformation,[],[f56])).
% 3.51/0.80  fof(f113,plain,(
% 3.51/0.80    ~spl2_1 | ~spl2_2),
% 3.51/0.80    inference(avatar_split_clause,[],[f62,f110,f106])).
% 3.51/0.80  fof(f62,plain,(
% 3.51/0.80    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 3.51/0.80    inference(cnf_transformation,[],[f56])).
% 3.51/0.80  % SZS output end Proof for theBenchmark
% 3.51/0.80  % (29153)------------------------------
% 3.51/0.80  % (29153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.51/0.80  % (29153)Termination reason: Refutation
% 3.51/0.80  
% 3.51/0.80  % (29153)Memory used [KB]: 9850
% 3.51/0.80  % (29153)Time elapsed: 0.376 s
% 3.51/0.80  % (29153)------------------------------
% 3.51/0.80  % (29153)------------------------------
% 3.51/0.81  % (29148)Success in time 0.46 s
%------------------------------------------------------------------------------
