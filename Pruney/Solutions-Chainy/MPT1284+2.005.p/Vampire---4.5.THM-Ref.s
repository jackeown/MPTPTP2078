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
% DateTime   : Thu Dec  3 13:13:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 447 expanded)
%              Number of leaves         :   28 ( 183 expanded)
%              Depth                    :   19
%              Number of atoms          :  601 (3059 expanded)
%              Number of equality atoms :   33 (  63 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f422,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f89,f103,f116,f156,f244,f250,f251,f259,f260,f277,f420,f421])).

fof(f421,plain,
    ( ~ spl7_14
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f252,f73,f212])).

fof(f212,plain,
    ( spl7_14
  <=> v5_tops_1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f73,plain,
    ( spl7_1
  <=> sP0(sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f252,plain,
    ( ~ v5_tops_1(sK6,sK4)
    | ~ spl7_1 ),
    inference(resolution,[],[f75,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ v5_tops_1(X1,X0) ) ),
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

fof(f24,plain,(
    ! [X1,X3] :
      ( ( ~ v5_tops_1(X3,X1)
        & v4_tops_1(X3,X1)
        & v4_pre_topc(X3,X1) )
      | ~ sP0(X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f75,plain,
    ( sP0(sK4,sK6)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f420,plain,
    ( spl7_14
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f419,f216,f153,f112,f212])).

fof(f112,plain,
    ( spl7_7
  <=> sP1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f153,plain,
    ( spl7_12
  <=> v4_pre_topc(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f216,plain,
    ( spl7_15
  <=> r1_tarski(k1_tops_1(sK4,sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f419,plain,
    ( v5_tops_1(sK6,sK4)
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f418,f113])).

fof(f113,plain,
    ( sP1(sK6,sK4)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f112])).

fof(f418,plain,
    ( v5_tops_1(sK6,sK4)
    | ~ sP1(sK6,sK4)
    | ~ spl7_12
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f417,f154])).

fof(f154,plain,
    ( v4_pre_topc(sK6,sK4)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f153])).

fof(f417,plain,
    ( v5_tops_1(sK6,sK4)
    | ~ v4_pre_topc(sK6,sK4)
    | ~ sP1(sK6,sK4)
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f416,f218])).

fof(f218,plain,
    ( r1_tarski(k1_tops_1(sK4,sK6),sK6)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f216])).

fof(f416,plain,
    ( v5_tops_1(sK6,sK4)
    | ~ r1_tarski(k1_tops_1(sK4,sK6),sK6)
    | ~ v4_pre_topc(sK6,sK4)
    | ~ sP1(sK6,sK4) ),
    inference(subsumption_resolution,[],[f407,f48])).

fof(f48,plain,(
    l1_pre_topc(sK4) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tops_1)).

fof(f407,plain,
    ( v5_tops_1(sK6,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ r1_tarski(k1_tops_1(sK4,sK6),sK6)
    | ~ v4_pre_topc(sK6,sK4)
    | ~ sP1(sK6,sK4) ),
    inference(resolution,[],[f402,f50])).

fof(f50,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f35])).

fof(f402,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v5_tops_1(X3,X2)
      | ~ l1_pre_topc(X2)
      | ~ r1_tarski(k1_tops_1(X2,X3),X3)
      | ~ v4_pre_topc(X3,X2)
      | ~ sP1(X3,X2) ) ),
    inference(trivial_inequality_removal,[],[f401])).

fof(f401,plain,(
    ! [X2,X3] :
      ( X3 != X3
      | v5_tops_1(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ r1_tarski(k1_tops_1(X2,X3),X3)
      | ~ v4_pre_topc(X3,X2)
      | ~ sP1(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f380])).

fof(f380,plain,(
    ! [X2,X3] :
      ( X3 != X3
      | v5_tops_1(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ r1_tarski(k1_tops_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v4_pre_topc(X3,X2)
      | ~ sP1(X3,X2) ) ),
    inference(superposition,[],[f57,f378])).

fof(f378,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
      | ~ r1_tarski(k1_tops_1(X1,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v4_pre_topc(X0,X1)
      | ~ sP1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f369])).

fof(f369,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ r1_tarski(k1_tops_1(X1,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0
      | ~ sP1(X0,X1) ) ),
    inference(resolution,[],[f266,f92])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
      | ~ sP1(X0,X1) ) ),
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

fof(f266,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(k2_pre_topc(X2,k1_tops_1(X2,X3)),X4)
      | ~ v4_pre_topc(X4,X2)
      | ~ r1_tarski(k1_tops_1(X2,X3),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k1_tops_1(X2,X3),X4)
      | ~ v4_pre_topc(X4,X2)
      | r1_tarski(k2_pre_topc(X2,k1_tops_1(X2,X3)),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f64,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | v5_tops_1(X1,X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(f277,plain,
    ( spl7_15
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f276,f137,f112,f216])).

fof(f137,plain,
    ( spl7_11
  <=> sK6 = k2_pre_topc(sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f276,plain,
    ( r1_tarski(k1_tops_1(sK4,sK6),sK6)
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f273,f113])).

fof(f273,plain,
    ( r1_tarski(k1_tops_1(sK4,sK6),sK6)
    | ~ sP1(sK6,sK4)
    | ~ spl7_11 ),
    inference(superposition,[],[f60,f139])).

fof(f139,plain,
    ( sK6 = k2_pre_topc(sK4,sK6)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f137])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f260,plain,
    ( spl7_12
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f254,f73,f153])).

fof(f254,plain,
    ( v4_pre_topc(sK6,sK4)
    | ~ spl7_1 ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f259,plain,
    ( spl7_6
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f253,f73,f108])).

fof(f108,plain,
    ( spl7_6
  <=> v4_tops_1(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f253,plain,
    ( v4_tops_1(sK6,sK4)
    | ~ spl7_1 ),
    inference(resolution,[],[f75,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v4_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f251,plain,
    ( ~ spl7_2
    | spl7_9 ),
    inference(avatar_split_clause,[],[f191,f127,f77])).

fof(f77,plain,
    ( spl7_2
  <=> v4_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f127,plain,
    ( spl7_9
  <=> sK5 = k2_pre_topc(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f191,plain,
    ( ~ v4_pre_topc(sK5,sK3)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f190,f47])).

fof(f47,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f190,plain,
    ( ~ v4_pre_topc(sK5,sK3)
    | ~ l1_pre_topc(sK3)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f147,f128])).

fof(f128,plain,
    ( sK5 != k2_pre_topc(sK3,sK5)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f147,plain,
    ( ~ v4_pre_topc(sK5,sK3)
    | sK5 = k2_pre_topc(sK3,sK5)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f54,f49])).

fof(f49,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f250,plain,
    ( spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f185,f86,f77])).

fof(f86,plain,
    ( spl7_4
  <=> v5_tops_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f185,plain,
    ( ~ v5_tops_1(sK5,sK3)
    | v4_pre_topc(sK5,sK3) ),
    inference(subsumption_resolution,[],[f184,f46])).

fof(f46,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f184,plain,
    ( ~ v2_pre_topc(sK3)
    | ~ v5_tops_1(sK5,sK3)
    | v4_pre_topc(sK5,sK3) ),
    inference(subsumption_resolution,[],[f180,f47])).

fof(f180,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ v5_tops_1(sK5,sK3)
    | v4_pre_topc(sK5,sK3) ),
    inference(resolution,[],[f179,f49])).

fof(f179,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | ~ v5_tops_1(X5,X4)
      | v4_pre_topc(X5,X4) ) ),
    inference(subsumption_resolution,[],[f177,f66])).

fof(f177,plain,(
    ! [X4,X5] :
      ( v4_pre_topc(X5,X4)
      | ~ m1_subset_1(k1_tops_1(X4,X5),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | ~ v5_tops_1(X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) ) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,(
    ! [X4,X5] :
      ( v4_pre_topc(X5,X4)
      | ~ m1_subset_1(k1_tops_1(X4,X5),k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | ~ v5_tops_1(X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4) ) ),
    inference(superposition,[],[f65,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f244,plain,
    ( ~ spl7_4
    | spl7_5
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f243])).

fof(f243,plain,
    ( $false
    | ~ spl7_4
    | spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f242,f47])).

fof(f242,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl7_4
    | spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f241,f49])).

fof(f241,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ spl7_4
    | spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f240,f88])).

fof(f88,plain,
    ( v5_tops_1(sK5,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f240,plain,
    ( ~ v5_tops_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ spl7_4
    | spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f239,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f239,plain,
    ( ~ r1_tarski(sK5,sK5)
    | ~ v5_tops_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ spl7_4
    | spl7_5
    | ~ spl7_9 ),
    inference(superposition,[],[f237,f56])).

fof(f237,plain,
    ( ~ r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5)))
    | ~ spl7_4
    | spl7_5
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f236,f102])).

fof(f102,plain,
    ( ~ sP1(sK5,sK3)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_5
  <=> sP1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f236,plain,
    ( ~ r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5)))
    | sP1(sK5,sK3)
    | ~ spl7_4
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f234,f209])).

fof(f209,plain,
    ( r1_tarski(k1_tops_1(sK3,sK5),sK5)
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f208,f88])).

fof(f208,plain,
    ( r1_tarski(k1_tops_1(sK3,sK5),sK5)
    | ~ v5_tops_1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f204,f47])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK3)
    | r1_tarski(k1_tops_1(sK3,sK5),sK5)
    | ~ v5_tops_1(sK5,sK3) ),
    inference(resolution,[],[f178,f49])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ v5_tops_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f144,f56])).

fof(f144,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X1,X0),k2_pre_topc(X1,k1_tops_1(X1,X0)))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | r1_tarski(k1_tops_1(X1,X0),k2_pre_topc(X1,k1_tops_1(X1,X0)))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f66,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f234,plain,
    ( ~ r1_tarski(k1_tops_1(sK3,sK5),sK5)
    | ~ r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5)))
    | sP1(sK5,sK3)
    | ~ spl7_9 ),
    inference(superposition,[],[f62,f129])).

fof(f129,plain,
    ( sK5 = k2_pre_topc(sK3,sK5)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
      | ~ r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f156,plain,
    ( spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f151,f153,f137])).

fof(f151,plain,
    ( ~ v4_pre_topc(sK6,sK4)
    | sK6 = k2_pre_topc(sK4,sK6) ),
    inference(subsumption_resolution,[],[f148,f48])).

fof(f148,plain,
    ( ~ v4_pre_topc(sK6,sK4)
    | sK6 = k2_pre_topc(sK4,sK6)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f54,f50])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:26:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (10693)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (10699)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (10688)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (10691)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (10693)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (10700)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (10709)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (10695)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (10707)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (10697)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (10713)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (10703)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (10694)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (10710)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (10702)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (10692)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (10711)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (10708)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (10689)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f422,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f84,f89,f103,f116,f156,f244,f250,f251,f259,f260,f277,f420,f421])).
% 0.21/0.53  fof(f421,plain,(
% 0.21/0.53    ~spl7_14 | ~spl7_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f252,f73,f212])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    spl7_14 <=> v5_tops_1(sK6,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    spl7_1 <=> sP0(sK4,sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    ~v5_tops_1(sK6,sK4) | ~spl7_1),
% 0.21/0.53    inference(resolution,[],[f75,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | ~v5_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : ((~v5_tops_1(X1,X0) & v4_tops_1(X1,X0) & v4_pre_topc(X1,X0)) | ~sP0(X0,X1))),
% 0.21/0.53    inference(rectify,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X1,X3] : ((~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X1,X3] : ((~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) | ~sP0(X1,X3))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    sP0(sK4,sK6) | ~spl7_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f73])).
% 0.21/0.53  fof(f420,plain,(
% 0.21/0.53    spl7_14 | ~spl7_7 | ~spl7_12 | ~spl7_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f419,f216,f153,f112,f212])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    spl7_7 <=> sP1(sK6,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    spl7_12 <=> v4_pre_topc(sK6,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    spl7_15 <=> r1_tarski(k1_tops_1(sK4,sK6),sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.53  fof(f419,plain,(
% 0.21/0.53    v5_tops_1(sK6,sK4) | (~spl7_7 | ~spl7_12 | ~spl7_15)),
% 0.21/0.53    inference(subsumption_resolution,[],[f418,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    sP1(sK6,sK4) | ~spl7_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f112])).
% 0.21/0.53  fof(f418,plain,(
% 0.21/0.53    v5_tops_1(sK6,sK4) | ~sP1(sK6,sK4) | (~spl7_12 | ~spl7_15)),
% 0.21/0.53    inference(subsumption_resolution,[],[f417,f154])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    v4_pre_topc(sK6,sK4) | ~spl7_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f153])).
% 0.21/0.53  fof(f417,plain,(
% 0.21/0.53    v5_tops_1(sK6,sK4) | ~v4_pre_topc(sK6,sK4) | ~sP1(sK6,sK4) | ~spl7_15),
% 0.21/0.53    inference(subsumption_resolution,[],[f416,f218])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK4,sK6),sK6) | ~spl7_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f216])).
% 0.21/0.53  fof(f416,plain,(
% 0.21/0.53    v5_tops_1(sK6,sK4) | ~r1_tarski(k1_tops_1(sK4,sK6),sK6) | ~v4_pre_topc(sK6,sK4) | ~sP1(sK6,sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f407,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    l1_pre_topc(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ((((((~v4_tops_1(sK5,sK3) | ~v4_pre_topc(sK5,sK3)) & v5_tops_1(sK5,sK3)) | sP0(sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f25,f34,f33,f32,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK3) | ~v4_pre_topc(X2,sK3)) & v5_tops_1(X2,sK3)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK3) | ~v4_pre_topc(X2,sK3)) & v5_tops_1(X2,sK3)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK3) | ~v4_pre_topc(X2,sK3)) & v5_tops_1(X2,sK3)) | sP0(sK4,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK4))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK3) | ~v4_pre_topc(X2,sK3)) & v5_tops_1(X2,sK3)) | sP0(sK4,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3)))) => (? [X3] : ((((~v4_tops_1(sK5,sK3) | ~v4_pre_topc(sK5,sK3)) & v5_tops_1(sK5,sK3)) | sP0(sK4,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ? [X3] : ((((~v4_tops_1(sK5,sK3) | ~v4_pre_topc(sK5,sK3)) & v5_tops_1(sK5,sK3)) | sP0(sK4,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))) => ((((~v4_tops_1(sK5,sK3) | ~v4_pre_topc(sK5,sK3)) & v5_tops_1(sK5,sK3)) | sP0(sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | sP0(X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(definition_folding,[],[f12,f24])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & v4_tops_1(X3,X1) & v4_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v4_pre_topc(X2,X0)) & v5_tops_1(X2,X0)) | (~v5_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v5_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v4_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v4_pre_topc(X3,X1)) => v5_tops_1(X3,X1)))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tops_1)).
% 0.21/0.53  fof(f407,plain,(
% 0.21/0.53    v5_tops_1(sK6,sK4) | ~l1_pre_topc(sK4) | ~r1_tarski(k1_tops_1(sK4,sK6),sK6) | ~v4_pre_topc(sK6,sK4) | ~sP1(sK6,sK4)),
% 0.21/0.53    inference(resolution,[],[f402,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f402,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v5_tops_1(X3,X2) | ~l1_pre_topc(X2) | ~r1_tarski(k1_tops_1(X2,X3),X3) | ~v4_pre_topc(X3,X2) | ~sP1(X3,X2)) )),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f401])).
% 0.21/0.53  fof(f401,plain,(
% 0.21/0.53    ( ! [X2,X3] : (X3 != X3 | v5_tops_1(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~r1_tarski(k1_tops_1(X2,X3),X3) | ~v4_pre_topc(X3,X2) | ~sP1(X3,X2)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f380])).
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    ( ! [X2,X3] : (X3 != X3 | v5_tops_1(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~r1_tarski(k1_tops_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~v4_pre_topc(X3,X2) | ~sP1(X3,X2)) )),
% 0.21/0.53    inference(superposition,[],[f57,f378])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 | ~r1_tarski(k1_tops_1(X1,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v4_pre_topc(X0,X1) | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f369])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v4_pre_topc(X0,X1) | ~r1_tarski(k1_tops_1(X1,X0),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f266,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(k2_pre_topc(X1,k1_tops_1(X1,X0)),X0) | k2_pre_topc(X1,k1_tops_1(X1,X0)) = X0 | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f61,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1] : ((sP1(X0,X1) | ~r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) | ~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)) & ((r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) & r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)) | ~sP1(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X1,X0] : ((sP1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~sP1(X1,X0)))),
% 0.21/0.53    inference(flattening,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X1,X0] : ((sP1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~sP1(X1,X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X1,X0] : (sP1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f266,plain,(
% 0.21/0.53    ( ! [X4,X2,X3] : (r1_tarski(k2_pre_topc(X2,k1_tops_1(X2,X3)),X4) | ~v4_pre_topc(X4,X2) | ~r1_tarski(k1_tops_1(X2,X3),X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f265])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    ( ! [X4,X2,X3] : (~r1_tarski(k1_tops_1(X2,X3),X4) | ~v4_pre_topc(X4,X2) | r1_tarski(k2_pre_topc(X2,k1_tops_1(X2,X3)),X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.21/0.53    inference(resolution,[],[f64,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_pre_topc(X0,X2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_tops_1)).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    spl7_15 | ~spl7_7 | ~spl7_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f276,f137,f112,f216])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    spl7_11 <=> sK6 = k2_pre_topc(sK4,sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK4,sK6),sK6) | (~spl7_7 | ~spl7_11)),
% 0.21/0.53    inference(subsumption_resolution,[],[f273,f113])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK4,sK6),sK6) | ~sP1(sK6,sK4) | ~spl7_11),
% 0.21/0.53    inference(superposition,[],[f60,f139])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    sK6 = k2_pre_topc(sK4,sK6) | ~spl7_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f137])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) | ~sP1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    spl7_12 | ~spl7_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f254,f73,f153])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    v4_pre_topc(sK6,sK4) | ~spl7_1),
% 0.21/0.53    inference(resolution,[],[f75,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | v4_pre_topc(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    spl7_6 | ~spl7_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f253,f73,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    spl7_6 <=> v4_tops_1(sK6,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    v4_tops_1(sK6,sK4) | ~spl7_1),
% 0.21/0.53    inference(resolution,[],[f75,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP0(X0,X1) | v4_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    ~spl7_2 | spl7_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f191,f127,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    spl7_2 <=> v4_pre_topc(sK5,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    spl7_9 <=> sK5 = k2_pre_topc(sK3,sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    ~v4_pre_topc(sK5,sK3) | spl7_9),
% 0.21/0.53    inference(subsumption_resolution,[],[f190,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    l1_pre_topc(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ~v4_pre_topc(sK5,sK3) | ~l1_pre_topc(sK3) | spl7_9),
% 0.21/0.53    inference(subsumption_resolution,[],[f147,f128])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    sK5 != k2_pre_topc(sK3,sK5) | spl7_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f127])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ~v4_pre_topc(sK5,sK3) | sK5 = k2_pre_topc(sK3,sK5) | ~l1_pre_topc(sK3)),
% 0.21/0.53    inference(resolution,[],[f54,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    spl7_2 | ~spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f185,f86,f77])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl7_4 <=> v5_tops_1(sK5,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ~v5_tops_1(sK5,sK3) | v4_pre_topc(sK5,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f184,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v2_pre_topc(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    ~v2_pre_topc(sK3) | ~v5_tops_1(sK5,sK3) | v4_pre_topc(sK5,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f180,f47])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | ~v5_tops_1(sK5,sK3) | v4_pre_topc(sK5,sK3)),
% 0.21/0.53    inference(resolution,[],[f179,f49])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | ~v5_tops_1(X5,X4) | v4_pre_topc(X5,X4)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f177,f66])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X4,X5] : (v4_pre_topc(X5,X4) | ~m1_subset_1(k1_tops_1(X4,X5),k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | ~v5_tops_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f175])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ( ! [X4,X5] : (v4_pre_topc(X5,X4) | ~m1_subset_1(k1_tops_1(X4,X5),k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | ~v5_tops_1(X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4)) )),
% 0.21/0.53    inference(superposition,[],[f65,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    ~spl7_4 | spl7_5 | ~spl7_9),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f243])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    $false | (~spl7_4 | spl7_5 | ~spl7_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f242,f47])).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    ~l1_pre_topc(sK3) | (~spl7_4 | spl7_5 | ~spl7_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f241,f49])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | (~spl7_4 | spl7_5 | ~spl7_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f240,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    v5_tops_1(sK5,sK3) | ~spl7_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    ~v5_tops_1(sK5,sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | (~spl7_4 | spl7_5 | ~spl7_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f239,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f239,plain,(
% 0.21/0.53    ~r1_tarski(sK5,sK5) | ~v5_tops_1(sK5,sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_pre_topc(sK3) | (~spl7_4 | spl7_5 | ~spl7_9)),
% 0.21/0.53    inference(superposition,[],[f237,f56])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    ~r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5))) | (~spl7_4 | spl7_5 | ~spl7_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f236,f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ~sP1(sK5,sK3) | spl7_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    spl7_5 <=> sP1(sK5,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.53  fof(f236,plain,(
% 0.21/0.53    ~r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5))) | sP1(sK5,sK3) | (~spl7_4 | ~spl7_9)),
% 0.21/0.53    inference(subsumption_resolution,[],[f234,f209])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK3,sK5),sK5) | ~spl7_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f208,f88])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK3,sK5),sK5) | ~v5_tops_1(sK5,sK3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f204,f47])).
% 0.21/0.53  fof(f204,plain,(
% 0.21/0.53    ~l1_pre_topc(sK3) | r1_tarski(k1_tops_1(sK3,sK5),sK5) | ~v5_tops_1(sK5,sK3)),
% 0.21/0.53    inference(resolution,[],[f178,f49])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1) | ~v5_tops_1(X1,X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f173])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(superposition,[],[f144,f56])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X1,X0),k2_pre_topc(X1,k1_tops_1(X1,X0))) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f141])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | r1_tarski(k1_tops_1(X1,X0),k2_pre_topc(X1,k1_tops_1(X1,X0))) | ~l1_pre_topc(X1)) )),
% 0.21/0.53    inference(resolution,[],[f66,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK3,sK5),sK5) | ~r1_tarski(sK5,k2_pre_topc(sK3,k1_tops_1(sK3,sK5))) | sP1(sK5,sK3) | ~spl7_9),
% 0.21/0.53    inference(superposition,[],[f62,f129])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    sK5 = k2_pre_topc(sK3,sK5) | ~spl7_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f127])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0) | ~r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0))) | sP1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    spl7_11 | ~spl7_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f151,f153,f137])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ~v4_pre_topc(sK6,sK4) | sK6 = k2_pre_topc(sK4,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f148,f48])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ~v4_pre_topc(sK6,sK4) | sK6 = k2_pre_topc(sK4,sK6) | ~l1_pre_topc(sK4)),
% 0.21/0.53    inference(resolution,[],[f54,f50])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    spl7_7 | ~spl7_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f106,f108,f112])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ~v4_tops_1(sK6,sK4) | sP1(sK6,sK4)),
% 0.21/0.53    inference(resolution,[],[f96,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP2(X0,X1) | ~v4_tops_1(X1,X0) | sP1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0,X1] : (((v4_tops_1(X1,X0) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v4_tops_1(X1,X0))) | ~sP2(X0,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : ((v4_tops_1(X1,X0) <=> sP1(X1,X0)) | ~sP2(X0,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    sP2(sK4,sK6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f94,f48])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    sP2(sK4,sK6) | ~l1_pre_topc(sK4)),
% 0.21/0.53    inference(resolution,[],[f63,f50])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (sP2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(definition_folding,[],[f17,f27,f26])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    spl7_3 | ~spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f97,f100,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    spl7_3 <=> v4_tops_1(sK5,sK3)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ~sP1(sK5,sK3) | v4_tops_1(sK5,sK3)),
% 0.21/0.53    inference(resolution,[],[f95,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v4_tops_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    sP2(sK3,sK5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f93,f47])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    sP2(sK3,sK5) | ~l1_pre_topc(sK3)),
% 0.21/0.53    inference(resolution,[],[f63,f49])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    spl7_1 | spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f51,f86,f73])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    v5_tops_1(sK5,sK3) | sP0(sK4,sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    spl7_1 | ~spl7_2 | ~spl7_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f52,f81,f77,f73])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ~v4_tops_1(sK5,sK3) | ~v4_pre_topc(sK5,sK3) | sP0(sK4,sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (10693)------------------------------
% 0.21/0.53  % (10693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10693)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (10693)Memory used [KB]: 6268
% 0.21/0.53  % (10693)Time elapsed: 0.092 s
% 0.21/0.53  % (10693)------------------------------
% 0.21/0.53  % (10693)------------------------------
% 0.21/0.53  % (10686)Success in time 0.169 s
%------------------------------------------------------------------------------
