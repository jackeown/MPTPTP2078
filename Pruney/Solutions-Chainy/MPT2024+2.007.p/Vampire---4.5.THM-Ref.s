%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  194 (1480 expanded)
%              Number of leaves         :   31 ( 621 expanded)
%              Depth                    :   28
%              Number of atoms          :  657 (8879 expanded)
%              Number of equality atoms :   11 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f666,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f170,f179,f195,f205,f322,f358,f383,f396,f431,f665])).

fof(f665,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f664])).

fof(f664,plain,
    ( $false
    | spl7_10 ),
    inference(subsumption_resolution,[],[f663,f64])).

fof(f64,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f48,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                    & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
                & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1)))
                & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1))) )
            & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1))) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,sK3)))
              & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3))) )
          & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3))) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,sK3)))
            & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3))) )
        & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3))) )
   => ( ? [X3] :
          ( ~ m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(sK2,sK3)))
          & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3))) )
      & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( ~ m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(sK2,sK3)))
        & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3))) )
   => ( ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))
      & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f663,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl7_10 ),
    inference(resolution,[],[f616,f194])).

fof(f194,plain,
    ( ~ sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl7_10
  <=> sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f616,plain,(
    ! [X1] :
      ( sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f615,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f615,plain,(
    ! [X1] :
      ( sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f614,f62])).

fof(f62,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f614,plain,(
    ! [X1] :
      ( sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f605,f63])).

fof(f63,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f605,plain,(
    ! [X1] :
      ( sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2)
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f599,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X1,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f22,f43,f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( sP0(X0,X2,X1)
    <=> ( v3_pre_topc(X2,X0)
        & r2_hidden(X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f43,plain,(
    ! [X1,X2,X0] :
      ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f599,plain,(
    m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f598,f263])).

fof(f263,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f262,f61])).

fof(f262,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f261,f62])).

fof(f261,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f260,f63])).

fof(f260,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f259,f64])).

fof(f259,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f254,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f254,plain,(
    m1_connsp_2(sK4,sK2,sK3) ),
    inference(subsumption_resolution,[],[f253,f61])).

fof(f253,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f252,f62])).

fof(f252,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f251,f63])).

fof(f251,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f246,f64])).

fof(f246,plain,
    ( m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f75,f65])).

fof(f65,plain,(
    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f598,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f592,f268])).

fof(f268,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f267,f61])).

fof(f267,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f266,f62])).

fof(f266,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f265,f63])).

fof(f265,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f264,f64])).

fof(f264,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f258,f86])).

fof(f258,plain,(
    m1_connsp_2(sK5,sK2,sK3) ),
    inference(subsumption_resolution,[],[f257,f61])).

fof(f257,plain,
    ( m1_connsp_2(sK5,sK2,sK3)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f256,f62])).

fof(f256,plain,
    ( m1_connsp_2(sK5,sK2,sK3)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f255,f63])).

fof(f255,plain,
    ( m1_connsp_2(sK5,sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f247,f64])).

fof(f247,plain,
    ( m1_connsp_2(sK5,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f75,f66])).

fof(f66,plain,(
    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f592,plain,
    ( m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(superposition,[],[f92,f583])).

fof(f583,plain,(
    k3_tarski(k2_tarski(sK4,sK5)) = k4_subset_1(u1_struct_0(sK2),sK4,sK5) ),
    inference(resolution,[],[f280,f263])).

fof(f280,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
      | k4_subset_1(u1_struct_0(sK2),X2,sK5) = k3_tarski(k2_tarski(X2,sK5)) ) ),
    inference(resolution,[],[f268,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f93,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f431,plain,
    ( ~ spl7_6
    | ~ spl7_8
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_8
    | spl7_12 ),
    inference(subsumption_resolution,[],[f429,f62])).

fof(f429,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ spl7_6
    | ~ spl7_8
    | spl7_12 ),
    inference(subsumption_resolution,[],[f428,f63])).

fof(f428,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_6
    | ~ spl7_8
    | spl7_12 ),
    inference(subsumption_resolution,[],[f427,f331])).

fof(f331,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f169,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ~ v3_pre_topc(X1,X0)
        | ~ r2_hidden(X2,X1) )
      & ( ( v3_pre_topc(X1,X0)
          & r2_hidden(X2,X1) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ~ v3_pre_topc(X2,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( v3_pre_topc(X2,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ~ v3_pre_topc(X2,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( v3_pre_topc(X2,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f169,plain,
    ( sP0(sK2,sK4,sK3)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f167])).

fof(f167,plain,
    ( spl7_6
  <=> sP0(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f427,plain,
    ( ~ v3_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_8
    | spl7_12 ),
    inference(subsumption_resolution,[],[f426,f263])).

fof(f426,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl7_8
    | spl7_12 ),
    inference(subsumption_resolution,[],[f425,f393])).

fof(f393,plain,
    ( v3_pre_topc(sK5,sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f178,f72])).

fof(f178,plain,
    ( sP0(sK2,sK5,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl7_8
  <=> sP0(sK2,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f425,plain,
    ( ~ v3_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl7_12 ),
    inference(subsumption_resolution,[],[f424,f268])).

fof(f424,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK5,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v3_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl7_12 ),
    inference(resolution,[],[f204,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f90,f79])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f204,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl7_12
  <=> v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f396,plain,
    ( ~ spl7_8
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | ~ spl7_8
    | spl7_11 ),
    inference(subsumption_resolution,[],[f394,f206])).

fof(f206,plain,
    ( ~ r2_hidden(sK3,sK5)
    | spl7_11 ),
    inference(resolution,[],[f200,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f144,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f88,f68])).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1))) ) ),
    inference(resolution,[],[f97,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f87,f68])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f89,f79])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f200,plain,
    ( ~ r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5)))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl7_11
  <=> r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f394,plain,
    ( r2_hidden(sK3,sK5)
    | ~ spl7_8 ),
    inference(resolution,[],[f178,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f383,plain,(
    ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f381,f123])).

fof(f123,plain,
    ( v1_xboole_0(sK4)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl7_4
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f381,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(resolution,[],[f377,f77])).

fof(f77,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f56,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
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

fof(f377,plain,(
    r2_hidden(sK3,sK4) ),
    inference(subsumption_resolution,[],[f376,f64])).

fof(f376,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,sK4) ),
    inference(resolution,[],[f306,f254])).

fof(f306,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(sK4,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_hidden(X4,sK4) ) ),
    inference(subsumption_resolution,[],[f305,f61])).

fof(f305,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(sK4,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_hidden(X4,sK4)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f304,f62])).

fof(f304,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(sK4,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_hidden(X4,sK4)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f299,f63])).

fof(f299,plain,(
    ! [X4] :
      ( ~ m1_connsp_2(sK4,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK2))
      | r2_hidden(X4,sK4)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f76,f263])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f358,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | spl7_7 ),
    inference(subsumption_resolution,[],[f353,f174])).

fof(f174,plain,
    ( ~ sP1(sK3,sK5,sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl7_7
  <=> sP1(sK3,sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f353,plain,(
    sP1(sK3,sK5,sK2) ),
    inference(resolution,[],[f286,f64])).

fof(f286,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X0,sK5,sK2) ) ),
    inference(subsumption_resolution,[],[f285,f61])).

fof(f285,plain,(
    ! [X0] :
      ( sP1(X0,sK5,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f284,f62])).

fof(f284,plain,(
    ! [X0] :
      ( sP1(X0,sK5,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f278,f63])).

fof(f278,plain,(
    ! [X0] :
      ( sP1(X0,sK5,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f268,f74])).

fof(f322,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f317,f165])).

fof(f165,plain,
    ( ~ sP1(sK3,sK4,sK2)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl7_5
  <=> sP1(sK3,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f317,plain,(
    sP1(sK3,sK4,sK2) ),
    inference(resolution,[],[f277,f64])).

fof(f277,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | sP1(X0,sK4,sK2) ) ),
    inference(subsumption_resolution,[],[f276,f61])).

fof(f276,plain,(
    ! [X0] :
      ( sP1(X0,sK4,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f275,f62])).

fof(f275,plain,(
    ! [X0] :
      ( sP1(X0,sK4,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f269,f63])).

fof(f269,plain,(
    ! [X0] :
      ( sP1(X0,sK4,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f263,f74])).

fof(f205,plain,
    ( ~ spl7_11
    | ~ spl7_12
    | spl7_9 ),
    inference(avatar_split_clause,[],[f196,f188,f202,f198])).

fof(f188,plain,
    ( spl7_9
  <=> sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f196,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2)
    | ~ r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5)))
    | spl7_9 ),
    inference(resolution,[],[f190,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f190,plain,
    ( ~ sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f188])).

fof(f195,plain,
    ( ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f186,f192,f188])).

fof(f186,plain,
    ( ~ sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2)
    | ~ sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3) ),
    inference(resolution,[],[f181,f94])).

fof(f94,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(definition_unfolding,[],[f67,f79])).

fof(f67,plain,(
    ~ m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(cnf_transformation,[],[f49])).

fof(f181,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(X4,u1_struct_0(k9_yellow_6(X3,X5)))
      | ~ sP1(X5,X4,X3)
      | ~ sP0(X3,X4,X5) ) ),
    inference(resolution,[],[f70,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f81,f77])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X2,X0] :
      ( ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f179,plain,
    ( ~ spl7_7
    | spl7_8
    | spl7_3 ),
    inference(avatar_split_clause,[],[f160,f117,f176,f172])).

fof(f117,plain,
    ( spl7_3
  <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f160,plain,
    ( sP0(sK2,sK5,sK3)
    | ~ sP1(sK3,sK5,sK2)
    | spl7_3 ),
    inference(resolution,[],[f69,f135])).

fof(f135,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | spl7_3 ),
    inference(subsumption_resolution,[],[f129,f119])).

fof(f119,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f129,plain,
    ( r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[],[f80,f66])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0)))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f170,plain,
    ( ~ spl7_5
    | spl7_6
    | spl7_3 ),
    inference(avatar_split_clause,[],[f159,f117,f167,f163])).

fof(f159,plain,
    ( sP0(sK2,sK4,sK3)
    | ~ sP1(sK3,sK4,sK2)
    | spl7_3 ),
    inference(resolution,[],[f69,f134])).

fof(f134,plain,
    ( r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | spl7_3 ),
    inference(subsumption_resolution,[],[f128,f119])).

fof(f128,plain,
    ( r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[],[f80,f65])).

fof(f124,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f104,f121,f117])).

fof(f104,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) ),
    inference(resolution,[],[f82,f65])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (28799)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (28812)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (28798)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (28817)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  % (28804)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (28808)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (28813)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (28803)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.48  % (28806)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (28797)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (28808)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f666,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f124,f170,f179,f195,f205,f322,f358,f383,f396,f431,f665])).
% 0.20/0.50  fof(f665,plain,(
% 0.20/0.50    spl7_10),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f664])).
% 0.20/0.50  fof(f664,plain,(
% 0.20/0.50    $false | spl7_10),
% 0.20/0.50    inference(subsumption_resolution,[],[f663,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.20/0.50    inference(cnf_transformation,[],[f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    (((~m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f20,f48,f47,f46,f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,X1)))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(sK2,sK3)))) => (? [X3] : (~m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3)))) & m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ? [X3] : (~m1_subset_1(k2_xboole_0(sK4,X3),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(sK2,sK3)))) => (~m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3))) & m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f17])).
% 0.20/0.50  fof(f17,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_waybel_9)).
% 0.20/0.50  fof(f663,plain,(
% 0.20/0.50    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl7_10),
% 0.20/0.50    inference(resolution,[],[f616,f194])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    ~sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2) | spl7_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f192])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    spl7_10 <=> sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.50  fof(f616,plain,(
% 0.20/0.50    ( ! [X1] : (sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~m1_subset_1(X1,u1_struct_0(sK2))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f615,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ~v2_struct_0(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f49])).
% 0.20/0.50  fof(f615,plain,(
% 0.20/0.50    ( ! [X1] : (sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f614,f62])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    v2_pre_topc(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f49])).
% 0.20/0.50  fof(f614,plain,(
% 0.20/0.50    ( ! [X1] : (sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f605,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    l1_pre_topc(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f49])).
% 0.20/0.50  fof(f605,plain,(
% 0.20/0.50    ( ! [X1] : (sP1(X1,k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(resolution,[],[f599,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X1,X2,X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (sP1(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(definition_folding,[],[f22,f43,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X2,X1] : (sP0(X0,X2,X1) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2)))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X1,X2,X0] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> sP0(X0,X2,X1)) | ~sP1(X1,X2,X0))),
% 0.20/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
% 0.20/0.50  fof(f599,plain,(
% 0.20/0.50    m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f598,f263])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f262,f61])).
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f261,f62])).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f260,f63])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f259,f64])).
% 0.20/0.50  fof(f259,plain,(
% 0.20/0.50    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(resolution,[],[f254,f86])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.20/0.50  fof(f254,plain,(
% 0.20/0.50    m1_connsp_2(sK4,sK2,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f253,f61])).
% 0.20/0.50  fof(f253,plain,(
% 0.20/0.50    m1_connsp_2(sK4,sK2,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f252,f62])).
% 0.20/0.50  fof(f252,plain,(
% 0.20/0.50    m1_connsp_2(sK4,sK2,sK3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f251,f63])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    m1_connsp_2(sK4,sK2,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f246,f64])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    m1_connsp_2(sK4,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(resolution,[],[f75,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    m1_subset_1(sK4,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.20/0.50    inference(cnf_transformation,[],[f49])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).
% 0.20/0.50  fof(f598,plain,(
% 0.20/0.50    m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f592,f268])).
% 0.20/0.50  fof(f268,plain,(
% 0.20/0.50    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.50    inference(subsumption_resolution,[],[f267,f61])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f266,f62])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f265,f63])).
% 0.20/0.50  fof(f265,plain,(
% 0.20/0.50    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f264,f64])).
% 0.20/0.50  fof(f264,plain,(
% 0.20/0.50    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(resolution,[],[f258,f86])).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    m1_connsp_2(sK5,sK2,sK3)),
% 0.20/0.50    inference(subsumption_resolution,[],[f257,f61])).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    m1_connsp_2(sK5,sK2,sK3) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f256,f62])).
% 0.20/0.50  fof(f256,plain,(
% 0.20/0.50    m1_connsp_2(sK5,sK2,sK3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f255,f63])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    m1_connsp_2(sK5,sK2,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f247,f64])).
% 0.20/0.50  fof(f247,plain,(
% 0.20/0.50    m1_connsp_2(sK5,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 0.20/0.50    inference(resolution,[],[f75,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    m1_subset_1(sK5,u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.20/0.50    inference(cnf_transformation,[],[f49])).
% 0.20/0.50  fof(f592,plain,(
% 0.20/0.50    m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.20/0.50    inference(superposition,[],[f92,f583])).
% 0.20/0.50  fof(f583,plain,(
% 0.20/0.50    k3_tarski(k2_tarski(sK4,sK5)) = k4_subset_1(u1_struct_0(sK2),sK4,sK5)),
% 0.20/0.50    inference(resolution,[],[f280,f263])).
% 0.20/0.50  fof(f280,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) | k4_subset_1(u1_struct_0(sK2),X2,sK5) = k3_tarski(k2_tarski(X2,sK5))) )),
% 0.20/0.50    inference(resolution,[],[f268,f99])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(definition_unfolding,[],[f93,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(flattening,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(flattening,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.20/0.50  fof(f431,plain,(
% 0.20/0.50    ~spl7_6 | ~spl7_8 | spl7_12),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f430])).
% 0.20/0.50  fof(f430,plain,(
% 0.20/0.50    $false | (~spl7_6 | ~spl7_8 | spl7_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f429,f62])).
% 0.20/0.50  fof(f429,plain,(
% 0.20/0.50    ~v2_pre_topc(sK2) | (~spl7_6 | ~spl7_8 | spl7_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f428,f63])).
% 0.20/0.50  fof(f428,plain,(
% 0.20/0.50    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl7_6 | ~spl7_8 | spl7_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f427,f331])).
% 0.20/0.50  fof(f331,plain,(
% 0.20/0.50    v3_pre_topc(sK4,sK2) | ~spl7_6),
% 0.20/0.50    inference(resolution,[],[f169,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v3_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1)) & ((v3_pre_topc(X1,X0) & r2_hidden(X2,X1)) | ~sP0(X0,X1,X2)))),
% 0.20/0.50    inference(rectify,[],[f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | ~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2)) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X2,X1)))),
% 0.20/0.50    inference(flattening,[],[f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ! [X0,X2,X1] : ((sP0(X0,X2,X1) | (~v3_pre_topc(X2,X0) | ~r2_hidden(X1,X2))) & ((v3_pre_topc(X2,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X2,X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f42])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    sP0(sK2,sK4,sK3) | ~spl7_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f167])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    spl7_6 <=> sP0(sK2,sK4,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.50  fof(f427,plain,(
% 0.20/0.50    ~v3_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl7_8 | spl7_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f426,f263])).
% 0.20/0.50  fof(f426,plain,(
% 0.20/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | (~spl7_8 | spl7_12)),
% 0.20/0.50    inference(subsumption_resolution,[],[f425,f393])).
% 0.20/0.50  fof(f393,plain,(
% 0.20/0.50    v3_pre_topc(sK5,sK2) | ~spl7_8),
% 0.20/0.50    inference(resolution,[],[f178,f72])).
% 0.20/0.50  fof(f178,plain,(
% 0.20/0.50    sP0(sK2,sK5,sK3) | ~spl7_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f176])).
% 0.20/0.50  fof(f176,plain,(
% 0.20/0.50    spl7_8 <=> sP0(sK2,sK5,sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.50  fof(f425,plain,(
% 0.20/0.50    ~v3_pre_topc(sK5,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl7_12),
% 0.20/0.50    inference(subsumption_resolution,[],[f424,f268])).
% 0.20/0.50  fof(f424,plain,(
% 0.20/0.50    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK5,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_pre_topc(sK4,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl7_12),
% 0.20/0.50    inference(resolution,[],[f204,f98])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f90,f79])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_tops_1)).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    ~v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2) | spl7_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f202])).
% 0.20/0.50  fof(f202,plain,(
% 0.20/0.50    spl7_12 <=> v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.50  fof(f396,plain,(
% 0.20/0.50    ~spl7_8 | spl7_11),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f395])).
% 0.20/0.50  fof(f395,plain,(
% 0.20/0.50    $false | (~spl7_8 | spl7_11)),
% 0.20/0.50    inference(subsumption_resolution,[],[f394,f206])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    ~r2_hidden(sK3,sK5) | spl7_11),
% 0.20/0.50    inference(resolution,[],[f200,f149])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_tarski(k2_tarski(X1,X2))) | ~r2_hidden(X0,X2)) )),
% 0.20/0.50    inference(resolution,[],[f144,f95])).
% 0.20/0.50  fof(f95,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f88,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f60])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.20/0.50    inference(nnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,k3_tarski(k2_tarski(X2,X1)))) )),
% 0.20/0.50    inference(resolution,[],[f97,f96])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f87,f68])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f60])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(definition_unfolding,[],[f89,f79])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.50  fof(f200,plain,(
% 0.20/0.50    ~r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5))) | spl7_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f198])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    spl7_11 <=> r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.50  fof(f394,plain,(
% 0.20/0.50    r2_hidden(sK3,sK5) | ~spl7_8),
% 0.20/0.50    inference(resolution,[],[f178,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X2,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f54])).
% 0.20/0.50  fof(f383,plain,(
% 0.20/0.50    ~spl7_4),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f382])).
% 0.20/0.50  fof(f382,plain,(
% 0.20/0.50    $false | ~spl7_4),
% 0.20/0.50    inference(subsumption_resolution,[],[f381,f123])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    v1_xboole_0(sK4) | ~spl7_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f121])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    spl7_4 <=> v1_xboole_0(sK4)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.50  fof(f381,plain,(
% 0.20/0.50    ~v1_xboole_0(sK4)),
% 0.20/0.50    inference(resolution,[],[f377,f77])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f56,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.50    inference(rectify,[],[f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.50  fof(f377,plain,(
% 0.20/0.50    r2_hidden(sK3,sK4)),
% 0.20/0.50    inference(subsumption_resolution,[],[f376,f64])).
% 0.20/0.50  fof(f376,plain,(
% 0.20/0.50    ~m1_subset_1(sK3,u1_struct_0(sK2)) | r2_hidden(sK3,sK4)),
% 0.20/0.50    inference(resolution,[],[f306,f254])).
% 0.20/0.50  fof(f306,plain,(
% 0.20/0.50    ( ! [X4] : (~m1_connsp_2(sK4,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK2)) | r2_hidden(X4,sK4)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f305,f61])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    ( ! [X4] : (~m1_connsp_2(sK4,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK2)) | r2_hidden(X4,sK4) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f304,f62])).
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    ( ! [X4] : (~m1_connsp_2(sK4,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK2)) | r2_hidden(X4,sK4) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f299,f63])).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    ( ! [X4] : (~m1_connsp_2(sK4,sK2,X4) | ~m1_subset_1(X4,u1_struct_0(sK2)) | r2_hidden(X4,sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(resolution,[],[f76,f263])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).
% 0.20/0.50  fof(f358,plain,(
% 0.20/0.50    spl7_7),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f357])).
% 0.20/0.50  fof(f357,plain,(
% 0.20/0.50    $false | spl7_7),
% 0.20/0.50    inference(subsumption_resolution,[],[f353,f174])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    ~sP1(sK3,sK5,sK2) | spl7_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f172])).
% 0.20/0.50  fof(f172,plain,(
% 0.20/0.50    spl7_7 <=> sP1(sK3,sK5,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.50  fof(f353,plain,(
% 0.20/0.50    sP1(sK3,sK5,sK2)),
% 0.20/0.50    inference(resolution,[],[f286,f64])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | sP1(X0,sK5,sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f285,f61])).
% 0.20/0.50  fof(f285,plain,(
% 0.20/0.50    ( ! [X0] : (sP1(X0,sK5,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f284,f62])).
% 0.20/0.50  fof(f284,plain,(
% 0.20/0.50    ( ! [X0] : (sP1(X0,sK5,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f278,f63])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    ( ! [X0] : (sP1(X0,sK5,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(resolution,[],[f268,f74])).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    spl7_5),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f321])).
% 0.20/0.50  fof(f321,plain,(
% 0.20/0.50    $false | spl7_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f317,f165])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ~sP1(sK3,sK4,sK2) | spl7_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f163])).
% 0.20/0.50  fof(f163,plain,(
% 0.20/0.50    spl7_5 <=> sP1(sK3,sK4,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.50  fof(f317,plain,(
% 0.20/0.50    sP1(sK3,sK4,sK2)),
% 0.20/0.50    inference(resolution,[],[f277,f64])).
% 0.20/0.50  fof(f277,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | sP1(X0,sK4,sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f276,f61])).
% 0.20/0.50  fof(f276,plain,(
% 0.20/0.50    ( ! [X0] : (sP1(X0,sK4,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f275,f62])).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    ( ! [X0] : (sP1(X0,sK4,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f269,f63])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    ( ! [X0] : (sP1(X0,sK4,sK2) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 0.20/0.50    inference(resolution,[],[f263,f74])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    ~spl7_11 | ~spl7_12 | spl7_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f196,f188,f202,f198])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    spl7_9 <=> sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ~v3_pre_topc(k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~r2_hidden(sK3,k3_tarski(k2_tarski(sK4,sK5))) | spl7_9),
% 0.20/0.50    inference(resolution,[],[f190,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f54])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    ~sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3) | spl7_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f188])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    ~spl7_9 | ~spl7_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f186,f192,f188])).
% 0.20/0.50  fof(f186,plain,(
% 0.20/0.50    ~sP1(sK3,k3_tarski(k2_tarski(sK4,sK5)),sK2) | ~sP0(sK2,k3_tarski(k2_tarski(sK4,sK5)),sK3)),
% 0.20/0.50    inference(resolution,[],[f181,f94])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ~m1_subset_1(k3_tarski(k2_tarski(sK4,sK5)),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.20/0.50    inference(definition_unfolding,[],[f67,f79])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    ~m1_subset_1(k2_xboole_0(sK4,sK5),u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.20/0.50    inference(cnf_transformation,[],[f49])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ( ! [X4,X5,X3] : (m1_subset_1(X4,u1_struct_0(k9_yellow_6(X3,X5))) | ~sP1(X5,X4,X3) | ~sP0(X3,X4,X5)) )),
% 0.20/0.50    inference(resolution,[],[f70,f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f81,f77])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f59])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(nnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))))) | ~sP1(X0,X1,X2))),
% 0.20/0.50    inference(rectify,[],[f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ! [X1,X2,X0] : (((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~sP0(X0,X2,X1)) & (sP0(X0,X2,X1) | ~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))))) | ~sP1(X1,X2,X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f43])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    ~spl7_7 | spl7_8 | spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f160,f117,f176,f172])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    spl7_3 <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    sP0(sK2,sK5,sK3) | ~sP1(sK3,sK5,sK2) | spl7_3),
% 0.20/0.50    inference(resolution,[],[f69,f135])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) | spl7_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f129,f119])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3))) | spl7_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f117])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    r2_hidden(sK5,u1_struct_0(k9_yellow_6(sK2,sK3))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.20/0.50    inference(resolution,[],[f80,f66])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f59])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X1,u1_struct_0(k9_yellow_6(X2,X0))) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f51])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    ~spl7_5 | spl7_6 | spl7_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f159,f117,f167,f163])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    sP0(sK2,sK4,sK3) | ~sP1(sK3,sK4,sK2) | spl7_3),
% 0.20/0.50    inference(resolution,[],[f69,f134])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) | spl7_3),
% 0.20/0.50    inference(subsumption_resolution,[],[f128,f119])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    r2_hidden(sK4,u1_struct_0(k9_yellow_6(sK2,sK3))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.20/0.50    inference(resolution,[],[f80,f65])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ~spl7_3 | spl7_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f104,f121,f117])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    v1_xboole_0(sK4) | ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK2,sK3)))),
% 0.20/0.50    inference(resolution,[],[f82,f65])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f59])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (28808)------------------------------
% 0.20/0.50  % (28808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (28808)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (28808)Memory used [KB]: 11129
% 0.20/0.50  % (28808)Time elapsed: 0.086 s
% 0.20/0.50  % (28808)------------------------------
% 0.20/0.50  % (28808)------------------------------
% 0.20/0.50  % (28814)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (28793)Success in time 0.145 s
%------------------------------------------------------------------------------
