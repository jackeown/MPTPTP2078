%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:05 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 426 expanded)
%              Number of leaves         :   26 ( 173 expanded)
%              Depth                    :   17
%              Number of atoms          :  540 (2973 expanded)
%              Number of equality atoms :   41 (  70 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f477,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f103,f116,f207,f219,f226,f227,f228,f415,f476])).

fof(f476,plain,
    ( ~ spl7_4
    | spl7_5
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f475])).

fof(f475,plain,
    ( $false
    | ~ spl7_4
    | spl7_5
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f474,f47])).

fof(f47,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ( ( ~ v4_tops_1(sK5,sK3)
          | ~ v4_pre_topc(sK5,sK3) )
        & v5_tops_1(sK5,sK3) )
      | sP0(sK4,sK6) )
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f34,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v4_pre_topc(X2,X0) )
                        & v5_tops_1(X2,X0) )
                      | sP0(X1,X3) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK3)
                        | ~ v4_pre_topc(X2,sK3) )
                      & v5_tops_1(X2,sK3) )
                    | sP0(X1,X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK3)
                      | ~ v4_pre_topc(X2,sK3) )
                    & v5_tops_1(X2,sK3) )
                  | sP0(X1,X3) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK3)
                    | ~ v4_pre_topc(X2,sK3) )
                  & v5_tops_1(X2,sK3) )
                | sP0(sK4,X3) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK3)
                  | ~ v4_pre_topc(X2,sK3) )
                & v5_tops_1(X2,sK3) )
              | sP0(sK4,X3) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK5,sK3)
                | ~ v4_pre_topc(sK5,sK3) )
              & v5_tops_1(sK5,sK3) )
            | sP0(sK4,X3) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK5,sK3)
              | ~ v4_pre_topc(sK5,sK3) )
            & v5_tops_1(sK5,sK3) )
          | sP0(sK4,X3) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ( ( ( ~ v4_tops_1(sK5,sK3)
            | ~ v4_pre_topc(sK5,sK3) )
          & v5_tops_1(sK5,sK3) )
        | sP0(sK4,sK6) )
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | sP0(X1,X3) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f12,f24])).

fof(f24,plain,(
    ! [X1,X3] :
      ( ( ~ v5_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v4_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v4_pre_topc(X2,X0) )
                      & v5_tops_1(X2,X0) )
                    | ( ~ v5_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v4_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v5_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v4_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v4_pre_topc(X3,X1) )
                       => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v5_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v4_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v4_pre_topc(X3,X1) )
                     => v5_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).

fof(f474,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl7_4
    | spl7_5
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f473,f49])).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f473,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ spl7_4
    | spl7_5
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f472,f88])).

fof(f88,plain,
    ( v5_tops_1(sK5,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl7_4
  <=> v5_tops_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f472,plain,
    ( ~ v5_tops_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | spl7_5
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f471,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f471,plain,
    ( ~ r1_tarski(sK5,sK5)
    | ~ v5_tops_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | spl7_5
    | ~ spl7_15 ),
    inference(superposition,[],[f427,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f427,plain,
    ( ~ r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5)))
    | spl7_5
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f426,f102])).

fof(f102,plain,
    ( ~ sP1(sK5,sK3)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_5
  <=> sP1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f426,plain,
    ( ~ r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5)))
    | sP1(sK5,sK3)
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f422,f119])).

fof(f119,plain,(
    r1_tarski(k1_tops_1(sK3,sK5),sK5) ),
    inference(subsumption_resolution,[],[f117,f47])).

fof(f117,plain,
    ( r1_tarski(k1_tops_1(sK3,sK5),sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f53,f49])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f422,plain,
    ( ~ r1_tarski(k1_tops_1(sK3,sK5),sK5)
    | ~ r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5)))
    | sP1(sK5,sK3)
    | ~ spl7_15 ),
    inference(superposition,[],[f62,f206])).

fof(f206,plain,
    ( sK5 = k2_pre_topc(sK3,sK5)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl7_15
  <=> sK5 = k2_pre_topc(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
        | ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) )
      & ( ( r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
          & r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
        | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
      & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
        | ~ sP1(X1,X0) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
        | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
      & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
        | ~ sP1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
        & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f415,plain,
    ( ~ spl7_13
    | ~ spl7_7
    | spl7_16 ),
    inference(avatar_split_clause,[],[f414,f213,f112,f157])).

fof(f157,plain,
    ( spl7_13
  <=> v4_pre_topc(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f112,plain,
    ( spl7_7
  <=> sP1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f213,plain,
    ( spl7_16
  <=> v5_tops_1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f414,plain,
    ( ~ v4_pre_topc(sK6,sK4)
    | ~ spl7_7
    | spl7_16 ),
    inference(subsumption_resolution,[],[f399,f113])).

fof(f113,plain,
    ( sP1(sK6,sK4)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f399,plain,
    ( ~ v4_pre_topc(sK6,sK4)
    | ~ sP1(sK6,sK4)
    | spl7_16 ),
    inference(subsumption_resolution,[],[f398,f48])).

fof(f48,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f398,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v4_pre_topc(sK6,sK4)
    | ~ sP1(sK6,sK4)
    | spl7_16 ),
    inference(subsumption_resolution,[],[f395,f215])).

fof(f215,plain,
    ( ~ v5_tops_1(sK6,sK4)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f213])).

fof(f395,plain,
    ( v5_tops_1(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v4_pre_topc(sK6,sK4)
    | ~ sP1(sK6,sK4) ),
    inference(resolution,[],[f389,f50])).

fof(f50,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f35])).

fof(f389,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v5_tops_1(X3,X2)
      | ~ l1_pre_topc(X2)
      | ~ v4_pre_topc(X3,X2)
      | ~ sP1(X3,X2) ) ),
    inference(trivial_inequality_removal,[],[f388])).

fof(f388,plain,(
    ! [X2,X3] :
      ( X3 != X3
      | v5_tops_1(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v4_pre_topc(X3,X2)
      | ~ sP1(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f367])).

% (16354)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f367,plain,(
    ! [X2,X3] :
      ( X3 != X3
      | v5_tops_1(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v4_pre_topc(X3,X2)
      | ~ sP1(X3,X2) ) ),
    inference(superposition,[],[f57,f364])).

fof(f364,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f363,f53])).

fof(f363,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ r1_tarski(k1_tops_1(X1,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
      | ~ sP1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ r1_tarski(k1_tops_1(X1,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
      | ~ sP1(X0,X1) ) ),
    inference(resolution,[],[f263,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X0)),X0)
      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
      | ~ sP1(X0,X1) ) ),
    inference(resolution,[],[f61,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f263,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k2_pre_topc(X2,k1_tops_1(X2,X3)),X4)
      | ~ v4_pre_topc(X4,X2)
      | ~ r1_tarski(k1_tops_1(X2,X3),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f262])).

fof(f262,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k1_tops_1(X2,X3),X4)
      | ~ v4_pre_topc(X4,X2)
      | r1_tarski(k2_pre_topc(X2,k1_tops_1(X2,X3)),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f64,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f228,plain,
    ( spl7_13
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f225,f73,f157])).

fof(f73,plain,
    ( spl7_1
  <=> sP0(sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f225,plain,
    ( v4_pre_topc(sK6,sK4)
    | ~ spl7_1 ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ v5_tops_1(X1,X0)
        & v4_tops_1(X1,X0)
        & v4_pre_topc(X1,X0) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X3] :
      ( ( ~ v5_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v4_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f75,plain,
    ( sP0(sK4,sK6)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f227,plain,
    ( spl7_6
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f224,f73,f108])).

fof(f108,plain,
    ( spl7_6
  <=> v4_tops_1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f224,plain,
    ( v4_tops_1(sK6,sK4)
    | ~ spl7_1 ),
    inference(resolution,[],[f75,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f226,plain,
    ( ~ spl7_16
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f223,f73,f213])).

% (16340)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f223,plain,
    ( ~ v5_tops_1(sK6,sK4)
    | ~ spl7_1 ),
    inference(resolution,[],[f75,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f219,plain,
    ( ~ spl7_4
    | spl7_2 ),
    inference(avatar_split_clause,[],[f194,f77,f86])).

fof(f77,plain,
    ( spl7_2
  <=> v4_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f194,plain,
    ( ~ v5_tops_1(sK5,sK3)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f188,f171])).

fof(f171,plain,
    ( sK5 != k2_pre_topc(sK3,sK5)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f170,f47])).

fof(f170,plain,
    ( sK5 != k2_pre_topc(sK3,sK5)
    | ~ l1_pre_topc(sK3)
    | spl7_2 ),
    inference(subsumption_resolution,[],[f169,f79])).

fof(f79,plain,
    ( ~ v4_pre_topc(sK5,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f169,plain,
    ( sK5 != k2_pre_topc(sK3,sK5)
    | v4_pre_topc(sK5,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f165,f46])).

fof(f46,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f165,plain,
    ( sK5 != k2_pre_topc(sK3,sK5)
    | ~ v2_pre_topc(sK3)
    | v4_pre_topc(sK5,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f55,f49])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f188,plain,
    ( ~ v5_tops_1(sK5,sK3)
    | sK5 = k2_pre_topc(sK3,sK5) ),
    inference(subsumption_resolution,[],[f184,f47])).

fof(f184,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v5_tops_1(sK5,sK3)
    | sK5 = k2_pre_topc(sK3,sK5) ),
    inference(resolution,[],[f183,f49])).

fof(f183,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v5_tops_1(X3,X2)
      | k2_pre_topc(X2,X3) = X3 ) ),
    inference(subsumption_resolution,[],[f182,f65])).

fof(f182,plain,(
    ! [X2,X3] :
      ( k2_pre_topc(X2,X3) = X3
      | ~ m1_subset_1(k1_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v5_tops_1(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X2,X3] :
      ( k2_pre_topc(X2,X3) = X3
      | ~ m1_subset_1(k1_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v5_tops_1(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f66,f56])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f207,plain,
    ( spl7_15
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f188,f86,f204])).

fof(f116,plain,
    ( spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f106,f108,f112])).

fof(f106,plain,
    ( ~ v4_tops_1(sK6,sK4)
    | sP1(sK6,sK4) ),
    inference(resolution,[],[f96,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v4_tops_1(X1,X0)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v4_tops_1(X1,X0)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v4_tops_1(X1,X0) ) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v4_tops_1(X1,X0)
      <=> sP1(X1,X0) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f96,plain,(
    sP2(sK4,sK6) ),
    inference(subsumption_resolution,[],[f94,f48])).

fof(f94,plain,
    ( sP2(sK4,sK6)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f63,f50])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f17,f27,f26])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).

fof(f103,plain,
    ( spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f97,f100,f81])).

fof(f81,plain,
    ( spl7_3
  <=> v4_tops_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f97,plain,
    ( ~ sP1(sK5,sK3)
    | v4_tops_1(sK5,sK3) ),
    inference(resolution,[],[f95,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    sP2(sK3,sK5) ),
    inference(subsumption_resolution,[],[f93,f47])).

fof(f93,plain,
    ( sP2(sK3,sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f63,f49])).

fof(f89,plain,
    ( spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f51,f86,f73])).

fof(f51,plain,
    ( v5_tops_1(sK5,sK3)
    | sP0(sK4,sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f52,f81,f77,f73])).

fof(f52,plain,
    ( ~ v4_tops_1(sK5,sK3)
    | ~ v4_pre_topc(sK5,sK3)
    | sP0(sK4,sK6) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:38:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (16343)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (16347)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (16363)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (16351)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (16364)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (16353)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (16342)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.23/0.52  % (16345)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.23/0.52  % (16341)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.23/0.52  % (16343)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.52  % SZS output start Proof for theBenchmark
% 1.23/0.52  fof(f477,plain,(
% 1.23/0.52    $false),
% 1.23/0.52    inference(avatar_sat_refutation,[],[f84,f89,f103,f116,f207,f219,f226,f227,f228,f415,f476])).
% 1.23/0.52  fof(f476,plain,(
% 1.23/0.52    ~spl7_4 | spl7_5 | ~spl7_15),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f475])).
% 1.23/0.52  fof(f475,plain,(
% 1.23/0.52    $false | (~spl7_4 | spl7_5 | ~spl7_15)),
% 1.23/0.52    inference(subsumption_resolution,[],[f474,f47])).
% 1.23/0.52  fof(f47,plain,(
% 1.23/0.52    l1_pre_topc(sK3)),
% 1.23/0.52    inference(cnf_transformation,[],[f35])).
% 1.23/0.52  fof(f35,plain,(
% 1.23/0.52    ((((((~v4_tops_1(sK5,sK3) | ~v4_pre_topc(sK5,sK3)) & v5_tops_1(sK5,sK3)) | sP0(sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f34,f33,f32,f31])).
% 1.23/0.52  fof(f31,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK3) | ~v4_pre_topc(X2,sK3)) & v5_tops_1(X2,sK3)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f32,plain,(
% 1.23/0.52    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK3) | ~v4_pre_topc(X2,sK3)) & v5_tops_1(X2,sK3)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK3) | ~v4_pre_topc(X2,sK3)) & v5_tops_1(X2,sK3)) | sP0(sK4,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK4))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f33,plain,(
% 1.23/0.52    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK3) | ~v4_pre_topc(X2,sK3)) & v5_tops_1(X2,sK3)) | sP0(sK4,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) => (? [X3] : ((((~v4_tops_1(sK5,sK3) | ~v4_pre_topc(sK5,sK3)) & v5_tops_1(sK5,sK3)) | sP0(sK4,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f34,plain,(
% 1.23/0.52    ? [X3] : ((((~v4_tops_1(sK5,sK3) | ~v4_pre_topc(sK5,sK3)) & v5_tops_1(sK5,sK3)) | sP0(sK4,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) => ((((~v4_tops_1(sK5,sK3) | ~v4_pre_topc(sK5,sK3)) & v5_tops_1(sK5,sK3)) | sP0(sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f25,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.23/0.52    inference(definition_folding,[],[f12,f24])).
% 1.23/0.52  fof(f24,plain,(
% 1.23/0.52    ! [X1,X3] : ((~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 1.23/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.23/0.52  fof(f12,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.23/0.52    inference(flattening,[],[f11])).
% 1.23/0.52  fof(f11,plain,(
% 1.23/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f10])).
% 1.23/0.52  fof(f10,negated_conjecture,(
% 1.23/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 1.23/0.52    inference(negated_conjecture,[],[f9])).
% 1.23/0.52  fof(f9,conjecture,(
% 1.23/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tops_1)).
% 1.23/0.52  fof(f474,plain,(
% 1.23/0.52    ~l1_pre_topc(sK3) | (~spl7_4 | spl7_5 | ~spl7_15)),
% 1.23/0.52    inference(subsumption_resolution,[],[f473,f49])).
% 1.23/0.52  fof(f49,plain,(
% 1.23/0.52    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.23/0.52    inference(cnf_transformation,[],[f35])).
% 1.23/0.52  fof(f473,plain,(
% 1.23/0.52    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | (~spl7_4 | spl7_5 | ~spl7_15)),
% 1.23/0.52    inference(subsumption_resolution,[],[f472,f88])).
% 1.23/0.52  fof(f88,plain,(
% 1.23/0.52    v5_tops_1(sK5,sK3) | ~spl7_4),
% 1.23/0.52    inference(avatar_component_clause,[],[f86])).
% 1.23/0.52  fof(f86,plain,(
% 1.23/0.52    spl7_4 <=> v5_tops_1(sK5,sK3)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.23/0.52  fof(f472,plain,(
% 1.23/0.52    ~v5_tops_1(sK5,sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | (spl7_5 | ~spl7_15)),
% 1.23/0.52    inference(subsumption_resolution,[],[f471,f70])).
% 1.23/0.52  fof(f70,plain,(
% 1.23/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.23/0.52    inference(equality_resolution,[],[f68])).
% 1.23/0.52  fof(f68,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.23/0.52    inference(cnf_transformation,[],[f42])).
% 1.23/0.52  fof(f42,plain,(
% 1.23/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.23/0.52    inference(flattening,[],[f41])).
% 1.23/0.52  fof(f41,plain,(
% 1.23/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.23/0.52    inference(nnf_transformation,[],[f1])).
% 1.23/0.52  fof(f1,axiom,(
% 1.23/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.23/0.52  fof(f471,plain,(
% 1.23/0.52    ~r1_tarski(sK5,sK5) | ~v5_tops_1(sK5,sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | (spl7_5 | ~spl7_15)),
% 1.23/0.52    inference(superposition,[],[f427,f56])).
% 1.23/0.52  fof(f56,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f36])).
% 1.23/0.52  fof(f36,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(nnf_transformation,[],[f16])).
% 1.23/0.52  fof(f16,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f5])).
% 1.23/0.52  fof(f5,axiom,(
% 1.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).
% 1.23/0.52  fof(f427,plain,(
% 1.23/0.52    ~r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5))) | (spl7_5 | ~spl7_15)),
% 1.23/0.52    inference(subsumption_resolution,[],[f426,f102])).
% 1.23/0.52  fof(f102,plain,(
% 1.23/0.52    ~sP1(sK5,sK3) | spl7_5),
% 1.23/0.52    inference(avatar_component_clause,[],[f100])).
% 1.23/0.52  fof(f100,plain,(
% 1.23/0.52    spl7_5 <=> sP1(sK5,sK3)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.23/0.52  fof(f426,plain,(
% 1.23/0.52    ~r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5))) | sP1(sK5,sK3) | ~spl7_15),
% 1.23/0.52    inference(subsumption_resolution,[],[f422,f119])).
% 1.23/0.52  fof(f119,plain,(
% 1.23/0.52    r1_tarski(k1_tops_1(sK3,sK5),sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f117,f47])).
% 1.23/0.52  fof(f117,plain,(
% 1.23/0.52    r1_tarski(k1_tops_1(sK3,sK5),sK5) | ~l1_pre_topc(sK3)),
% 1.23/0.52    inference(resolution,[],[f53,f49])).
% 1.23/0.52  fof(f53,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f13])).
% 1.23/0.52  fof(f13,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f8])).
% 1.23/0.52  fof(f8,axiom,(
% 1.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.23/0.52  fof(f422,plain,(
% 1.23/0.52    ~r1_tarski(k1_tops_1(sK3,sK5),sK5) | ~r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5))) | sP1(sK5,sK3) | ~spl7_15),
% 1.23/0.52    inference(superposition,[],[f62,f206])).
% 1.23/0.52  fof(f206,plain,(
% 1.23/0.52    sK5 = k2_pre_topc(sK3,sK5) | ~spl7_15),
% 1.23/0.52    inference(avatar_component_clause,[],[f204])).
% 1.23/0.52  fof(f204,plain,(
% 1.23/0.52    spl7_15 <=> sK5 = k2_pre_topc(sK3,sK5)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.23/0.52  fof(f62,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) | ~r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) | sP1(X0,X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f40])).
% 1.23/0.52  fof(f40,plain,(
% 1.23/0.52    ! [X0,X1] : ((sP1(X0,X1) | ~r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) | ~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)) & ((r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) & r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)) | ~sP1(X0,X1)))),
% 1.23/0.52    inference(rectify,[],[f39])).
% 1.23/0.52  fof(f39,plain,(
% 1.23/0.52    ! [X1,X0] : ((sP1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~sP1(X1,X0)))),
% 1.23/0.52    inference(flattening,[],[f38])).
% 1.23/0.52  fof(f38,plain,(
% 1.23/0.52    ! [X1,X0] : ((sP1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~sP1(X1,X0)))),
% 1.23/0.52    inference(nnf_transformation,[],[f26])).
% 1.23/0.52  fof(f26,plain,(
% 1.23/0.52    ! [X1,X0] : (sP1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))),
% 1.23/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.23/0.52  fof(f415,plain,(
% 1.23/0.52    ~spl7_13 | ~spl7_7 | spl7_16),
% 1.23/0.52    inference(avatar_split_clause,[],[f414,f213,f112,f157])).
% 1.23/0.52  fof(f157,plain,(
% 1.23/0.52    spl7_13 <=> v4_pre_topc(sK6,sK4)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.23/0.52  fof(f112,plain,(
% 1.23/0.52    spl7_7 <=> sP1(sK6,sK4)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.23/0.52  fof(f213,plain,(
% 1.23/0.52    spl7_16 <=> v5_tops_1(sK6,sK4)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.23/0.52  fof(f414,plain,(
% 1.23/0.52    ~v4_pre_topc(sK6,sK4) | (~spl7_7 | spl7_16)),
% 1.23/0.52    inference(subsumption_resolution,[],[f399,f113])).
% 1.23/0.52  fof(f113,plain,(
% 1.23/0.52    sP1(sK6,sK4) | ~spl7_7),
% 1.23/0.52    inference(avatar_component_clause,[],[f112])).
% 1.23/0.52  fof(f399,plain,(
% 1.23/0.52    ~v4_pre_topc(sK6,sK4) | ~sP1(sK6,sK4) | spl7_16),
% 1.23/0.52    inference(subsumption_resolution,[],[f398,f48])).
% 1.23/0.52  fof(f48,plain,(
% 1.23/0.52    l1_pre_topc(sK4)),
% 1.23/0.52    inference(cnf_transformation,[],[f35])).
% 1.23/0.52  fof(f398,plain,(
% 1.23/0.52    ~l1_pre_topc(sK4) | ~v4_pre_topc(sK6,sK4) | ~sP1(sK6,sK4) | spl7_16),
% 1.23/0.52    inference(subsumption_resolution,[],[f395,f215])).
% 1.23/0.52  fof(f215,plain,(
% 1.23/0.52    ~v5_tops_1(sK6,sK4) | spl7_16),
% 1.23/0.52    inference(avatar_component_clause,[],[f213])).
% 1.23/0.52  fof(f395,plain,(
% 1.23/0.52    v5_tops_1(sK6,sK4) | ~l1_pre_topc(sK4) | ~v4_pre_topc(sK6,sK4) | ~sP1(sK6,sK4)),
% 1.23/0.52    inference(resolution,[],[f389,f50])).
% 1.23/0.52  fof(f50,plain,(
% 1.23/0.52    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 1.23/0.52    inference(cnf_transformation,[],[f35])).
% 1.23/0.52  fof(f389,plain,(
% 1.23/0.52    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v5_tops_1(X3,X2) | ~l1_pre_topc(X2) | ~v4_pre_topc(X3,X2) | ~sP1(X3,X2)) )),
% 1.23/0.52    inference(trivial_inequality_removal,[],[f388])).
% 1.23/0.52  fof(f388,plain,(
% 1.23/0.52    ( ! [X2,X3] : (X3 != X3 | v5_tops_1(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v4_pre_topc(X3,X2) | ~sP1(X3,X2)) )),
% 1.23/0.52    inference(duplicate_literal_removal,[],[f367])).
% 1.23/0.52  % (16354)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.23/0.52  fof(f367,plain,(
% 1.23/0.52    ( ! [X2,X3] : (X3 != X3 | v5_tops_1(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v4_pre_topc(X3,X2) | ~sP1(X3,X2)) )),
% 1.23/0.52    inference(superposition,[],[f57,f364])).
% 1.23/0.52  fof(f364,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v4_pre_topc(X0,X1) | ~sP1(X0,X1)) )),
% 1.23/0.52    inference(subsumption_resolution,[],[f363,f53])).
% 1.23/0.52  fof(f363,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~v4_pre_topc(X0,X1) | ~r1_tarski(k1_tops_1(X1,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 | ~sP1(X0,X1)) )),
% 1.23/0.52    inference(duplicate_literal_removal,[],[f354])).
% 1.23/0.52  fof(f354,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~v4_pre_topc(X0,X1) | ~r1_tarski(k1_tops_1(X1,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 | ~sP1(X0,X1)) )),
% 1.23/0.52    inference(resolution,[],[f263,f92])).
% 1.23/0.52  fof(f92,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X0)),X0) | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 | ~sP1(X0,X1)) )),
% 1.23/0.52    inference(resolution,[],[f61,f69])).
% 1.23/0.52  fof(f69,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f42])).
% 1.23/0.52  fof(f61,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) | ~sP1(X0,X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f40])).
% 1.23/0.52  fof(f263,plain,(
% 1.23/0.52    ( ! [X4,X2,X3] : (r1_tarski(k2_pre_topc(X2,k1_tops_1(X2,X3)),X4) | ~v4_pre_topc(X4,X2) | ~r1_tarski(k1_tops_1(X2,X3),X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.23/0.52    inference(duplicate_literal_removal,[],[f262])).
% 1.23/0.52  fof(f262,plain,(
% 1.23/0.52    ( ! [X4,X2,X3] : (~r1_tarski(k1_tops_1(X2,X3),X4) | ~v4_pre_topc(X4,X2) | r1_tarski(k2_pre_topc(X2,k1_tops_1(X2,X3)),X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.23/0.52    inference(resolution,[],[f64,f65])).
% 1.23/0.52  fof(f65,plain,(
% 1.23/0.52    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f21])).
% 1.23/0.52  fof(f21,plain,(
% 1.23/0.52    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(flattening,[],[f20])).
% 1.23/0.52  fof(f20,plain,(
% 1.23/0.52    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f6])).
% 1.23/0.52  fof(f6,axiom,(
% 1.23/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.23/0.52  fof(f64,plain,(
% 1.23/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_pre_topc(X0,X2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f19,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(flattening,[],[f18])).
% 1.23/0.52  fof(f18,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f7])).
% 1.23/0.52  fof(f7,axiom,(
% 1.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tops_1)).
% 1.23/0.52  fof(f57,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f36])).
% 1.23/0.52  fof(f228,plain,(
% 1.23/0.52    spl7_13 | ~spl7_1),
% 1.23/0.52    inference(avatar_split_clause,[],[f225,f73,f157])).
% 1.23/0.52  fof(f73,plain,(
% 1.23/0.52    spl7_1 <=> sP0(sK4,sK6)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.23/0.52  fof(f225,plain,(
% 1.23/0.52    v4_pre_topc(sK6,sK4) | ~spl7_1),
% 1.23/0.52    inference(resolution,[],[f75,f43])).
% 1.23/0.52  fof(f43,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~sP0(X0,X1) | v4_pre_topc(X1,X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f30])).
% 1.23/0.52  fof(f30,plain,(
% 1.23/0.52    ! [X0,X1] : ((~v5_tops_1(X1,X0) & v4_tops_1(X1,X0) & v4_pre_topc(X1,X0)) | ~sP0(X0,X1))),
% 1.23/0.52    inference(rectify,[],[f29])).
% 1.23/0.52  fof(f29,plain,(
% 1.23/0.52    ! [X1,X3] : ((~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 1.23/0.52    inference(nnf_transformation,[],[f24])).
% 1.23/0.52  fof(f75,plain,(
% 1.23/0.52    sP0(sK4,sK6) | ~spl7_1),
% 1.23/0.52    inference(avatar_component_clause,[],[f73])).
% 1.23/0.52  fof(f227,plain,(
% 1.23/0.52    spl7_6 | ~spl7_1),
% 1.23/0.52    inference(avatar_split_clause,[],[f224,f73,f108])).
% 1.23/0.52  fof(f108,plain,(
% 1.23/0.52    spl7_6 <=> v4_tops_1(sK6,sK4)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.23/0.52  fof(f224,plain,(
% 1.23/0.52    v4_tops_1(sK6,sK4) | ~spl7_1),
% 1.23/0.52    inference(resolution,[],[f75,f44])).
% 1.23/0.52  fof(f44,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~sP0(X0,X1) | v4_tops_1(X1,X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f30])).
% 1.23/0.52  fof(f226,plain,(
% 1.23/0.52    ~spl7_16 | ~spl7_1),
% 1.23/0.52    inference(avatar_split_clause,[],[f223,f73,f213])).
% 1.23/0.52  % (16340)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.52  fof(f223,plain,(
% 1.23/0.52    ~v5_tops_1(sK6,sK4) | ~spl7_1),
% 1.23/0.52    inference(resolution,[],[f75,f45])).
% 1.23/0.52  fof(f45,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~sP0(X0,X1) | ~v5_tops_1(X1,X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f30])).
% 1.23/0.52  fof(f219,plain,(
% 1.23/0.52    ~spl7_4 | spl7_2),
% 1.23/0.52    inference(avatar_split_clause,[],[f194,f77,f86])).
% 1.23/0.52  fof(f77,plain,(
% 1.23/0.52    spl7_2 <=> v4_pre_topc(sK5,sK3)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.23/0.52  fof(f194,plain,(
% 1.23/0.52    ~v5_tops_1(sK5,sK3) | spl7_2),
% 1.23/0.52    inference(subsumption_resolution,[],[f188,f171])).
% 1.23/0.52  fof(f171,plain,(
% 1.23/0.52    sK5 != k2_pre_topc(sK3,sK5) | spl7_2),
% 1.23/0.52    inference(subsumption_resolution,[],[f170,f47])).
% 1.23/0.52  fof(f170,plain,(
% 1.23/0.52    sK5 != k2_pre_topc(sK3,sK5) | ~l1_pre_topc(sK3) | spl7_2),
% 1.23/0.52    inference(subsumption_resolution,[],[f169,f79])).
% 1.23/0.52  fof(f79,plain,(
% 1.23/0.52    ~v4_pre_topc(sK5,sK3) | spl7_2),
% 1.23/0.52    inference(avatar_component_clause,[],[f77])).
% 1.23/0.52  fof(f169,plain,(
% 1.23/0.52    sK5 != k2_pre_topc(sK3,sK5) | v4_pre_topc(sK5,sK3) | ~l1_pre_topc(sK3)),
% 1.23/0.52    inference(subsumption_resolution,[],[f165,f46])).
% 1.23/0.52  fof(f46,plain,(
% 1.23/0.52    v2_pre_topc(sK3)),
% 1.23/0.52    inference(cnf_transformation,[],[f35])).
% 1.23/0.52  fof(f165,plain,(
% 1.23/0.52    sK5 != k2_pre_topc(sK3,sK5) | ~v2_pre_topc(sK3) | v4_pre_topc(sK5,sK3) | ~l1_pre_topc(sK3)),
% 1.23/0.52    inference(resolution,[],[f55,f49])).
% 1.23/0.52  fof(f55,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f15])).
% 1.23/0.52  fof(f15,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(flattening,[],[f14])).
% 1.23/0.52  fof(f14,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f3])).
% 1.23/0.52  fof(f3,axiom,(
% 1.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.23/0.52  fof(f188,plain,(
% 1.23/0.52    ~v5_tops_1(sK5,sK3) | sK5 = k2_pre_topc(sK3,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f184,f47])).
% 1.23/0.52  fof(f184,plain,(
% 1.23/0.52    ~l1_pre_topc(sK3) | ~v5_tops_1(sK5,sK3) | sK5 = k2_pre_topc(sK3,sK5)),
% 1.23/0.52    inference(resolution,[],[f183,f49])).
% 1.23/0.52  fof(f183,plain,(
% 1.23/0.52    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v5_tops_1(X3,X2) | k2_pre_topc(X2,X3) = X3) )),
% 1.23/0.52    inference(subsumption_resolution,[],[f182,f65])).
% 1.23/0.52  fof(f182,plain,(
% 1.23/0.52    ( ! [X2,X3] : (k2_pre_topc(X2,X3) = X3 | ~m1_subset_1(k1_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v5_tops_1(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.23/0.52    inference(duplicate_literal_removal,[],[f180])).
% 1.23/0.52  fof(f180,plain,(
% 1.23/0.52    ( ! [X2,X3] : (k2_pre_topc(X2,X3) = X3 | ~m1_subset_1(k1_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v5_tops_1(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.23/0.52    inference(superposition,[],[f66,f56])).
% 1.23/0.52  fof(f66,plain,(
% 1.23/0.52    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f23])).
% 1.23/0.52  fof(f23,plain,(
% 1.23/0.52    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(flattening,[],[f22])).
% 1.23/0.52  fof(f22,plain,(
% 1.23/0.52    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f2])).
% 1.23/0.52  fof(f2,axiom,(
% 1.23/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 1.23/0.52  fof(f207,plain,(
% 1.23/0.52    spl7_15 | ~spl7_4),
% 1.23/0.52    inference(avatar_split_clause,[],[f188,f86,f204])).
% 1.23/0.52  fof(f116,plain,(
% 1.23/0.52    spl7_7 | ~spl7_6),
% 1.23/0.52    inference(avatar_split_clause,[],[f106,f108,f112])).
% 1.23/0.52  fof(f106,plain,(
% 1.23/0.52    ~v4_tops_1(sK6,sK4) | sP1(sK6,sK4)),
% 1.23/0.52    inference(resolution,[],[f96,f58])).
% 1.23/0.52  fof(f58,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~sP2(X0,X1) | ~v4_tops_1(X1,X0) | sP1(X1,X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f37])).
% 1.23/0.52  fof(f37,plain,(
% 1.23/0.52    ! [X0,X1] : (((v4_tops_1(X1,X0) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v4_tops_1(X1,X0))) | ~sP2(X0,X1))),
% 1.23/0.52    inference(nnf_transformation,[],[f27])).
% 1.23/0.52  fof(f27,plain,(
% 1.23/0.52    ! [X0,X1] : ((v4_tops_1(X1,X0) <=> sP1(X1,X0)) | ~sP2(X0,X1))),
% 1.23/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.23/0.52  fof(f96,plain,(
% 1.23/0.52    sP2(sK4,sK6)),
% 1.23/0.52    inference(subsumption_resolution,[],[f94,f48])).
% 1.23/0.52  fof(f94,plain,(
% 1.23/0.52    sP2(sK4,sK6) | ~l1_pre_topc(sK4)),
% 1.23/0.52    inference(resolution,[],[f63,f50])).
% 1.23/0.52  fof(f63,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f28])).
% 1.23/0.52  fof(f28,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : (sP2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(definition_folding,[],[f17,f27,f26])).
% 1.23/0.52  fof(f17,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f4])).
% 1.23/0.52  fof(f4,axiom,(
% 1.23/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 1.23/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_tops_1)).
% 1.23/0.52  fof(f103,plain,(
% 1.23/0.52    spl7_3 | ~spl7_5),
% 1.23/0.52    inference(avatar_split_clause,[],[f97,f100,f81])).
% 1.23/0.52  fof(f81,plain,(
% 1.23/0.52    spl7_3 <=> v4_tops_1(sK5,sK3)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.23/0.52  fof(f97,plain,(
% 1.23/0.52    ~sP1(sK5,sK3) | v4_tops_1(sK5,sK3)),
% 1.23/0.52    inference(resolution,[],[f95,f59])).
% 1.23/0.52  fof(f59,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v4_tops_1(X1,X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f37])).
% 1.23/0.52  fof(f95,plain,(
% 1.23/0.52    sP2(sK3,sK5)),
% 1.23/0.52    inference(subsumption_resolution,[],[f93,f47])).
% 1.23/0.52  fof(f93,plain,(
% 1.23/0.52    sP2(sK3,sK5) | ~l1_pre_topc(sK3)),
% 1.23/0.52    inference(resolution,[],[f63,f49])).
% 1.23/0.52  fof(f89,plain,(
% 1.23/0.52    spl7_1 | spl7_4),
% 1.23/0.52    inference(avatar_split_clause,[],[f51,f86,f73])).
% 1.23/0.52  fof(f51,plain,(
% 1.23/0.52    v5_tops_1(sK5,sK3) | sP0(sK4,sK6)),
% 1.23/0.52    inference(cnf_transformation,[],[f35])).
% 1.23/0.52  fof(f84,plain,(
% 1.23/0.52    spl7_1 | ~spl7_2 | ~spl7_3),
% 1.23/0.52    inference(avatar_split_clause,[],[f52,f81,f77,f73])).
% 1.23/0.52  fof(f52,plain,(
% 1.23/0.52    ~v4_tops_1(sK5,sK3) | ~v4_pre_topc(sK5,sK3) | sP0(sK4,sK6)),
% 1.23/0.52    inference(cnf_transformation,[],[f35])).
% 1.23/0.52  % SZS output end Proof for theBenchmark
% 1.23/0.52  % (16343)------------------------------
% 1.23/0.52  % (16343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (16343)Termination reason: Refutation
% 1.23/0.52  
% 1.23/0.52  % (16343)Memory used [KB]: 6396
% 1.23/0.52  % (16343)Time elapsed: 0.107 s
% 1.23/0.52  % (16343)------------------------------
% 1.23/0.52  % (16343)------------------------------
% 1.23/0.52  % (16344)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.23/0.52  % (16338)Success in time 0.163 s
%------------------------------------------------------------------------------
