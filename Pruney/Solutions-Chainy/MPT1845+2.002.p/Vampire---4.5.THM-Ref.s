%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 873 expanded)
%              Number of leaves         :   30 ( 296 expanded)
%              Depth                    :   16
%              Number of atoms          :  538 (3982 expanded)
%              Number of equality atoms :   33 ( 839 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f66,f93,f102,f107,f112,f123,f144,f159,f164,f179,f196,f199,f213,f218,f235,f238,f243,f253])).

fof(f253,plain,(
    ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl8_18 ),
    inference(resolution,[],[f234,f35])).

fof(f35,plain,(
    ~ v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ v2_pre_topc(sK4)
    & v2_pre_topc(sK3)
    & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    & l1_pre_topc(sK4)
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f8,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_pre_topc(X1)
            & v2_pre_topc(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(sK3)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ~ v2_pre_topc(X1)
        & v2_pre_topc(sK3)
        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
        & l1_pre_topc(X1) )
   => ( ~ v2_pre_topc(sK4)
      & v2_pre_topc(sK3)
      & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_pre_topc(X1)
          & v2_pre_topc(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v2_pre_topc(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v2_pre_topc(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v2_pre_topc(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v2_pre_topc(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).

fof(f234,plain,
    ( v2_pre_topc(sK4)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl8_18
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f243,plain,
    ( ~ spl8_15
    | ~ spl8_16
    | ~ spl8_2
    | spl8_13 ),
    inference(avatar_split_clause,[],[f242,f183,f61,f215,f193])).

fof(f193,plain,
    ( spl8_15
  <=> r1_tarski(sK5(sK4),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f215,plain,
    ( spl8_16
  <=> m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f61,plain,
    ( spl8_2
  <=> sP1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f183,plain,
    ( spl8_13
  <=> r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f242,plain,
    ( ~ m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ r1_tarski(sK5(sK4),u1_pre_topc(sK3))
    | ~ spl8_2
    | spl8_13 ),
    inference(resolution,[],[f185,f169])).

fof(f169,plain,
    ( ! [X0] :
        ( r2_hidden(k5_setfam_1(u1_struct_0(sK3),X0),u1_pre_topc(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
        | ~ r1_tarski(X0,u1_pre_topc(sK3)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f40,f63])).

fof(f63,plain,
    ( sP1(sK3)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ sP1(X0)
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
          & r1_tarski(sK5(X0),u1_pre_topc(X0))
          & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X2] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r1_tarski(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
        & r1_tarski(sK5(X0),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X1] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            & r1_tarski(X1,u1_pre_topc(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X2] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r1_tarski(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( sP1(X0)
        | ~ sP0(X0)
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP1(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ( sP0(X0)
        & ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f185,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3))
    | spl8_13 ),
    inference(avatar_component_clause,[],[f183])).

fof(f238,plain,(
    spl8_17 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl8_17 ),
    inference(resolution,[],[f236,f32])).

fof(f32,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f19])).

fof(f236,plain,
    ( ~ l1_pre_topc(sK4)
    | spl8_17 ),
    inference(resolution,[],[f230,f51])).

fof(f51,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f11,f15,f14,f13])).

fof(f13,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP1(X0) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f230,plain,
    ( ~ sP2(sK4)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl8_17
  <=> sP2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f235,plain,
    ( ~ spl8_17
    | spl8_18
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f221,f114,f232,f228])).

fof(f114,plain,
    ( spl8_9
  <=> sP1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f221,plain,
    ( v2_pre_topc(sK4)
    | ~ sP2(sK4)
    | ~ spl8_9 ),
    inference(resolution,[],[f115,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | v2_pre_topc(X0)
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP1(X0) )
        & ( sP1(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f115,plain,
    ( sP1(sK4)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f218,plain,
    ( spl8_9
    | spl8_16
    | ~ spl8_14
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f210,f99,f86,f187,f215,f114])).

fof(f187,plain,
    ( spl8_14
  <=> r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f86,plain,
    ( spl8_3
  <=> sP0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f99,plain,
    ( spl8_6
  <=> m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f210,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | sP1(sK4)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f209,f75])).

fof(f75,plain,(
    u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | u1_struct_0(sK3) = u1_struct_0(sK4) ),
    inference(superposition,[],[f71,f33])).

fof(f33,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
      | u1_struct_0(sK3) = X0 ) ),
    inference(resolution,[],[f69,f31])).

fof(f31,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = X1
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2) ) ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f209,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3))
    | m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | sP1(sK4)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f208,f134])).

fof(f134,plain,
    ( u1_pre_topc(sK3) = u1_pre_topc(sK4)
    | ~ spl8_6 ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
        | u1_pre_topc(sK4) = X1 )
    | ~ spl8_6 ),
    inference(superposition,[],[f125,f77])).

fof(f77,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK4)) ),
    inference(backward_demodulation,[],[f33,f75])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK4))
        | u1_pre_topc(sK4) = X1 )
    | ~ spl8_6 ),
    inference(resolution,[],[f101,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f208,plain,
    ( m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | sP1(sK4)
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f201,f75])).

fof(f201,plain,
    ( sP1(sK4)
    | m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl8_3 ),
    inference(resolution,[],[f88,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | sP1(X0)
      | m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f88,plain,
    ( sP0(sK4)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f213,plain,
    ( ~ spl8_6
    | ~ spl8_10
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl8_6
    | ~ spl8_10
    | spl8_14 ),
    inference(resolution,[],[f189,f145])).

fof(f145,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ spl8_6
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f120,f134])).

fof(f120,plain,
    ( r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_10
  <=> r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f189,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | spl8_14 ),
    inference(avatar_component_clause,[],[f187])).

fof(f199,plain,
    ( spl8_9
    | ~ spl8_3
    | ~ spl8_13
    | ~ spl8_14
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f198,f99,f187,f183,f86,f114])).

fof(f198,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3))
    | ~ sP0(sK4)
    | sP1(sK4)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f197,f134])).

fof(f197,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3))
    | ~ sP0(sK4)
    | sP1(sK4)
    | ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f146,f134])).

fof(f146,plain,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK4))
    | ~ sP0(sK4)
    | sP1(sK4)
    | ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) ),
    inference(superposition,[],[f44,f75])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0))
      | ~ sP0(X0)
      | sP1(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f196,plain,
    ( spl8_9
    | ~ spl8_3
    | spl8_15
    | ~ spl8_14
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f191,f99,f187,f193,f86,f114])).

fof(f191,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | r1_tarski(sK5(sK4),u1_pre_topc(sK3))
    | ~ sP0(sK4)
    | sP1(sK4)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f149,f75])).

fof(f149,plain,
    ( r1_tarski(sK5(sK4),u1_pre_topc(sK3))
    | ~ sP0(sK4)
    | sP1(sK4)
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3))
    | ~ spl8_6 ),
    inference(superposition,[],[f43,f134])).

fof(f43,plain,(
    ! [X0] :
      ( r1_tarski(sK5(X0),u1_pre_topc(X0))
      | ~ sP0(X0)
      | sP1(X0)
      | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f179,plain,
    ( ~ spl8_12
    | ~ spl8_8
    | ~ spl8_7
    | ~ spl8_11
    | ~ spl8_2
    | spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f177,f99,f90,f61,f156,f104,f109,f161])).

fof(f161,plain,
    ( spl8_12
  <=> r2_hidden(sK7(sK4),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f109,plain,
    ( spl8_8
  <=> m1_subset_1(sK6(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f104,plain,
    ( spl8_7
  <=> m1_subset_1(sK7(sK4),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f156,plain,
    ( spl8_11
  <=> r2_hidden(sK6(sK4),u1_pre_topc(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f90,plain,
    ( spl8_4
  <=> r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f177,plain,
    ( ~ r2_hidden(sK6(sK4),u1_pre_topc(sK3))
    | ~ m1_subset_1(sK7(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK6(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK7(sK4),u1_pre_topc(sK3))
    | ~ spl8_2
    | spl8_4
    | ~ spl8_6 ),
    inference(resolution,[],[f176,f136])).

fof(f136,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK3))
    | spl8_4
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f92,f134])).

fof(f92,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK4))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k9_subset_1(u1_struct_0(sK3),X1,X0),u1_pre_topc(sK3))
        | ~ r2_hidden(X1,u1_pre_topc(sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ r2_hidden(X0,u1_pre_topc(sK3)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f45,f68])).

fof(f68,plain,
    ( sP0(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f63,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X4,X0,X3] :
      ( ~ sP0(X0)
      | ~ r2_hidden(X4,u1_pre_topc(X0))
      | ~ r2_hidden(X3,u1_pre_topc(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),sK7(X0)),u1_pre_topc(X0))
          & r2_hidden(sK7(X0),u1_pre_topc(X0))
          & r2_hidden(sK6(X0),u1_pre_topc(X0))
          & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
                | ~ r2_hidden(X4,u1_pre_topc(X0))
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f29,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK6(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK6(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),sK7(X0)),u1_pre_topc(X0))
        & r2_hidden(sK7(X0),u1_pre_topc(X0))
        & r2_hidden(sK6(X0),u1_pre_topc(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))
                | ~ r2_hidden(X4,u1_pre_topc(X0))
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X1] :
            ( ! [X2] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                | ~ r2_hidden(X2,u1_pre_topc(X0))
                | ~ r2_hidden(X1,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f164,plain,
    ( spl8_3
    | spl8_12
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f152,f99,f161,f86])).

fof(f152,plain,
    ( r2_hidden(sK7(sK4),u1_pre_topc(sK3))
    | sP0(sK4)
    | ~ spl8_6 ),
    inference(superposition,[],[f49,f134])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f159,plain,
    ( spl8_3
    | spl8_11
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f151,f99,f156,f86])).

fof(f151,plain,
    ( r2_hidden(sK6(sK4),u1_pre_topc(sK3))
    | sP0(sK4)
    | ~ spl8_6 ),
    inference(superposition,[],[f48,f134])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f144,plain,
    ( ~ spl8_2
    | ~ spl8_6
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_6
    | spl8_10 ),
    inference(resolution,[],[f142,f63])).

fof(f142,plain,
    ( ~ sP1(sK3)
    | ~ spl8_6
    | spl8_10 ),
    inference(resolution,[],[f138,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

% (4318)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (4326)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (4321)Refutation not found, incomplete strategy% (4321)------------------------------
% (4321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4337)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (4338)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (4321)Termination reason: Refutation not found, incomplete strategy

% (4321)Memory used [KB]: 10618
% (4321)Time elapsed: 0.109 s
% (4321)------------------------------
% (4321)------------------------------
% (4333)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (4330)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (4335)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (4314)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (4312)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f138,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))
    | ~ spl8_6
    | spl8_10 ),
    inference(backward_demodulation,[],[f119,f134])).

fof(f119,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))
    | spl8_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f123,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl8_5 ),
    inference(resolution,[],[f97,f32])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK4)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl8_5
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f112,plain,
    ( spl8_3
    | spl8_8 ),
    inference(avatar_split_clause,[],[f83,f109,f86])).

fof(f83,plain,
    ( m1_subset_1(sK6(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | sP0(sK4) ),
    inference(superposition,[],[f46,f75])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,
    ( spl8_3
    | spl8_7 ),
    inference(avatar_split_clause,[],[f82,f104,f86])).

fof(f82,plain,
    ( m1_subset_1(sK7(sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | sP0(sK4) ),
    inference(superposition,[],[f47,f75])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f102,plain,
    ( ~ spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f81,f99,f95])).

fof(f81,plain,
    ( m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ l1_pre_topc(sK4) ),
    inference(superposition,[],[f36,f75])).

fof(f93,plain,
    ( spl8_3
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f80,f90,f86])).

fof(f80,plain,
    ( ~ r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK4))
    | sP0(sK4) ),
    inference(superposition,[],[f50,f75])).

fof(f50,plain,(
    ! [X0] :
      ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),sK7(X0)),u1_pre_topc(X0))
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f59,f31])).

fof(f59,plain,
    ( ~ l1_pre_topc(sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl8_1
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f64,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f55,f61,f57])).

fof(f55,plain,
    ( sP1(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f54,f34])).

fof(f34,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f37,f51])).

fof(f37,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | ~ v2_pre_topc(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (4320)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.46  % (4320)Refutation not found, incomplete strategy% (4320)------------------------------
% 0.21/0.46  % (4320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (4320)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (4320)Memory used [KB]: 10618
% 0.21/0.46  % (4320)Time elapsed: 0.064 s
% 0.21/0.46  % (4320)------------------------------
% 0.21/0.46  % (4320)------------------------------
% 0.21/0.50  % (4323)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (4336)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.50  % (4311)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (4321)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (4315)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (4322)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (4317)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (4339)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (4329)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (4322)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f64,f66,f93,f102,f107,f112,f123,f144,f159,f164,f179,f196,f199,f213,f218,f235,f238,f243,f253])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ~spl8_18),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f251])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    $false | ~spl8_18),
% 0.21/0.51    inference(resolution,[],[f234,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ~v2_pre_topc(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    (~v2_pre_topc(sK4) & v2_pre_topc(sK3) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) & l1_pre_topc(sK4)) & l1_pre_topc(sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f8,f18,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (~v2_pre_topc(X1) & v2_pre_topc(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v2_pre_topc(X1) & v2_pre_topc(sK3) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & l1_pre_topc(X1)) & l1_pre_topc(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X1] : (~v2_pre_topc(X1) & v2_pre_topc(sK3) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & l1_pre_topc(X1)) => (~v2_pre_topc(sK4) & v2_pre_topc(sK3) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) & l1_pre_topc(sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (~v2_pre_topc(X1) & v2_pre_topc(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : ((~v2_pre_topc(X1) & (v2_pre_topc(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_pre_topc(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_pre_topc(X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v2_pre_topc(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_pre_topc(X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tex_2)).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    v2_pre_topc(sK4) | ~spl8_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f232])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    spl8_18 <=> v2_pre_topc(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    ~spl8_15 | ~spl8_16 | ~spl8_2 | spl8_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f242,f183,f61,f215,f193])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    spl8_15 <=> r1_tarski(sK5(sK4),u1_pre_topc(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    spl8_16 <=> m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl8_2 <=> sP1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    spl8_13 <=> r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ~m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | ~r1_tarski(sK5(sK4),u1_pre_topc(sK3)) | (~spl8_2 | spl8_13)),
% 0.21/0.51    inference(resolution,[],[f185,f169])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(k5_setfam_1(u1_struct_0(sK3),X0),u1_pre_topc(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | ~r1_tarski(X0,u1_pre_topc(sK3))) ) | ~spl8_2),
% 0.21/0.51    inference(resolution,[],[f40,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    sP1(sK3) | ~spl8_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f61])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0] : (~sP1(X0) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : ((sP1(X0) | ~sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) & r1_tarski(sK5(X0),u1_pre_topc(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : ((sP1(X0) | ~sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 0.21/0.51    inference(rectify,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : ((sP1(X0) | ~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : ((sP1(X0) | (~sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP1(X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (sP1(X0) <=> (sP0(X0) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    ~r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3)) | spl8_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f183])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    spl8_17),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f237])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    $false | spl8_17),
% 0.21/0.51    inference(resolution,[],[f236,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    l1_pre_topc(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ~l1_pre_topc(sK4) | spl8_17),
% 0.21/0.51    inference(resolution,[],[f230,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0] : (sP2(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (sP2(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(definition_folding,[],[f11,f15,f14,f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (sP0(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : ((v2_pre_topc(X0) <=> sP1(X0)) | ~sP2(X0))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.51    inference(rectify,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    ~sP2(sK4) | spl8_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f228])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    spl8_17 <=> sP2(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    ~spl8_17 | spl8_18 | ~spl8_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f221,f114,f232,f228])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl8_9 <=> sP1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    v2_pre_topc(sK4) | ~sP2(sK4) | ~spl8_9),
% 0.21/0.51    inference(resolution,[],[f115,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (~sP1(X0) | v2_pre_topc(X0) | ~sP2(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (((v2_pre_topc(X0) | ~sP1(X0)) & (sP1(X0) | ~v2_pre_topc(X0))) | ~sP2(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f15])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    sP1(sK4) | ~spl8_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f114])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    spl8_9 | spl8_16 | ~spl8_14 | ~spl8_3 | ~spl8_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f210,f99,f86,f187,f215,f114])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    spl8_14 <=> r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl8_3 <=> sP0(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl8_6 <=> m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) | m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | sP1(sK4) | (~spl8_3 | ~spl8_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f209,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    u1_struct_0(sK3) = u1_struct_0(sK4)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | u1_struct_0(sK3) = u1_struct_0(sK4)),
% 0.21/0.51    inference(superposition,[],[f71,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | u1_struct_0(sK3) = X0) )),
% 0.21/0.51    inference(resolution,[],[f69,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    l1_pre_topc(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | u1_struct_0(X0) = X1 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(X1,X2)) )),
% 0.21/0.51    inference(resolution,[],[f52,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    ~r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3)) | m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | sP1(sK4) | (~spl8_3 | ~spl8_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f208,f134])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    u1_pre_topc(sK3) = u1_pre_topc(sK4) | ~spl8_6),
% 0.21/0.51    inference(equality_resolution,[],[f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) | u1_pre_topc(sK4) = X1) ) | ~spl8_6),
% 0.21/0.51    inference(superposition,[],[f125,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK4))),
% 0.21/0.51    inference(backward_demodulation,[],[f33,f75])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK4)) | u1_pre_topc(sK4) = X1) ) | ~spl8_6),
% 0.21/0.51    inference(resolution,[],[f101,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | ~spl8_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | sP1(sK4) | ~r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~spl8_3),
% 0.21/0.51    inference(forward_demodulation,[],[f201,f75])).
% 0.21/0.51  fof(f201,plain,(
% 0.21/0.51    sP1(sK4) | m1_subset_1(sK5(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) | ~r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~spl8_3),
% 0.21/0.51    inference(resolution,[],[f88,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0] : (~sP0(X0) | sP1(X0) | m1_subset_1(sK5(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    sP0(sK4) | ~spl8_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    ~spl8_6 | ~spl8_10 | spl8_14),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    $false | (~spl8_6 | ~spl8_10 | spl8_14)),
% 0.21/0.51    inference(resolution,[],[f189,f145])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) | (~spl8_6 | ~spl8_10)),
% 0.21/0.51    inference(forward_demodulation,[],[f120,f134])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | ~spl8_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl8_10 <=> r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) | spl8_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f187])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    spl8_9 | ~spl8_3 | ~spl8_13 | ~spl8_14 | ~spl8_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f198,f99,f187,f183,f86,f114])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) | ~r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3)) | ~sP0(sK4) | sP1(sK4) | ~spl8_6),
% 0.21/0.51    inference(forward_demodulation,[],[f197,f134])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ~r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK3)) | ~sP0(sK4) | sP1(sK4) | ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | ~spl8_6),
% 0.21/0.51    inference(forward_demodulation,[],[f146,f134])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ~r2_hidden(k5_setfam_1(u1_struct_0(sK3),sK5(sK4)),u1_pre_topc(sK4)) | ~sP0(sK4) | sP1(sK4) | ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4))),
% 0.21/0.51    inference(superposition,[],[f44,f75])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK5(X0)),u1_pre_topc(X0)) | ~sP0(X0) | sP1(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    spl8_9 | ~spl8_3 | spl8_15 | ~spl8_14 | ~spl8_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f191,f99,f187,f193,f86,f114])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) | r1_tarski(sK5(sK4),u1_pre_topc(sK3)) | ~sP0(sK4) | sP1(sK4) | ~spl8_6),
% 0.21/0.51    inference(forward_demodulation,[],[f149,f75])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    r1_tarski(sK5(sK4),u1_pre_topc(sK3)) | ~sP0(sK4) | sP1(sK4) | ~r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK3)) | ~spl8_6),
% 0.21/0.51    inference(superposition,[],[f43,f134])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(sK5(X0),u1_pre_topc(X0)) | ~sP0(X0) | sP1(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    ~spl8_12 | ~spl8_8 | ~spl8_7 | ~spl8_11 | ~spl8_2 | spl8_4 | ~spl8_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f177,f99,f90,f61,f156,f104,f109,f161])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    spl8_12 <=> r2_hidden(sK7(sK4),u1_pre_topc(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl8_8 <=> m1_subset_1(sK6(sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl8_7 <=> m1_subset_1(sK7(sK4),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    spl8_11 <=> r2_hidden(sK6(sK4),u1_pre_topc(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl8_4 <=> r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ~r2_hidden(sK6(sK4),u1_pre_topc(sK3)) | ~m1_subset_1(sK7(sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK6(sK4),k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(sK7(sK4),u1_pre_topc(sK3)) | (~spl8_2 | spl8_4 | ~spl8_6)),
% 0.21/0.51    inference(resolution,[],[f176,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK3)) | (spl8_4 | ~spl8_6)),
% 0.21/0.51    inference(backward_demodulation,[],[f92,f134])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK4)) | spl8_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(k9_subset_1(u1_struct_0(sK3),X1,X0),u1_pre_topc(sK3)) | ~r2_hidden(X1,u1_pre_topc(sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) | ~r2_hidden(X0,u1_pre_topc(sK3))) ) | ~spl8_2),
% 0.21/0.51    inference(resolution,[],[f45,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    sP0(sK3) | ~spl8_2),
% 0.21/0.51    inference(resolution,[],[f63,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (~sP1(X0) | sP0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X4,X0,X3] : (~sP0(X0) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : ((sP0(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),sK7(X0)),u1_pre_topc(X0)) & r2_hidden(sK7(X0),u1_pre_topc(X0)) & r2_hidden(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (! [X4] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f29,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),sK7(X0)),u1_pre_topc(X0)) & r2_hidden(sK7(X0),u1_pre_topc(X0)) & r2_hidden(sK6(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (! [X4] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X3,X4),u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.21/0.51    inference(rectify,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : ((sP0(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f13])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl8_3 | spl8_12 | ~spl8_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f152,f99,f161,f86])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    r2_hidden(sK7(sK4),u1_pre_topc(sK3)) | sP0(sK4) | ~spl8_6),
% 0.21/0.51    inference(superposition,[],[f49,f134])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK7(X0),u1_pre_topc(X0)) | sP0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    spl8_3 | spl8_11 | ~spl8_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f151,f99,f156,f86])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    r2_hidden(sK6(sK4),u1_pre_topc(sK3)) | sP0(sK4) | ~spl8_6),
% 0.21/0.51    inference(superposition,[],[f48,f134])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK6(X0),u1_pre_topc(X0)) | sP0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ~spl8_2 | ~spl8_6 | spl8_10),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f143])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    $false | (~spl8_2 | ~spl8_6 | spl8_10)),
% 0.21/0.51    inference(resolution,[],[f142,f63])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    ~sP1(sK3) | (~spl8_6 | spl8_10)),
% 0.21/0.51    inference(resolution,[],[f138,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  % (4318)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (4326)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (4321)Refutation not found, incomplete strategy% (4321)------------------------------
% 0.21/0.51  % (4321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4337)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (4338)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (4321)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4321)Memory used [KB]: 10618
% 0.21/0.52  % (4321)Time elapsed: 0.109 s
% 0.21/0.52  % (4321)------------------------------
% 0.21/0.52  % (4321)------------------------------
% 0.21/0.52  % (4333)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (4330)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (4335)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (4314)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (4312)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK3)) | (~spl8_6 | spl8_10)),
% 0.21/0.53    inference(backward_demodulation,[],[f119,f134])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ~r2_hidden(u1_struct_0(sK3),u1_pre_topc(sK4)) | spl8_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f118])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    spl8_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    $false | spl8_5),
% 0.21/0.53    inference(resolution,[],[f97,f32])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ~l1_pre_topc(sK4) | spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    spl8_5 <=> l1_pre_topc(sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    spl8_3 | spl8_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f83,f109,f86])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    m1_subset_1(sK6(sK4),k1_zfmisc_1(u1_struct_0(sK3))) | sP0(sK4)),
% 0.21/0.53    inference(superposition,[],[f46,f75])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl8_3 | spl8_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f82,f104,f86])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    m1_subset_1(sK7(sK4),k1_zfmisc_1(u1_struct_0(sK3))) | sP0(sK4)),
% 0.21/0.53    inference(superposition,[],[f47,f75])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) | sP0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ~spl8_5 | spl8_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f81,f99,f95])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) | ~l1_pre_topc(sK4)),
% 0.21/0.53    inference(superposition,[],[f36,f75])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl8_3 | ~spl8_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f80,f90,f86])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~r2_hidden(k9_subset_1(u1_struct_0(sK3),sK6(sK4),sK7(sK4)),u1_pre_topc(sK4)) | sP0(sK4)),
% 0.21/0.53    inference(superposition,[],[f50,f75])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK6(X0),sK7(X0)),u1_pre_topc(X0)) | sP0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    spl8_1),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    $false | spl8_1),
% 0.21/0.53    inference(resolution,[],[f59,f31])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ~l1_pre_topc(sK3) | spl8_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    spl8_1 <=> l1_pre_topc(sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ~spl8_1 | spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f55,f61,f57])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    sP1(sK3) | ~l1_pre_topc(sK3)),
% 0.21/0.53    inference(resolution,[],[f54,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    v2_pre_topc(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(X0) | sP1(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(resolution,[],[f37,f51])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (~sP2(X0) | ~v2_pre_topc(X0) | sP1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (4322)------------------------------
% 0.21/0.53  % (4322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4322)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (4322)Memory used [KB]: 6268
% 0.21/0.53  % (4322)Time elapsed: 0.114 s
% 0.21/0.53  % (4322)------------------------------
% 0.21/0.53  % (4322)------------------------------
% 0.21/0.53  % (4309)Success in time 0.177 s
%------------------------------------------------------------------------------
