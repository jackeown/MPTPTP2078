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
% DateTime   : Thu Dec  3 13:14:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 340 expanded)
%              Number of leaves         :   19 ( 128 expanded)
%              Depth                    :   17
%              Number of atoms          :  363 (2514 expanded)
%              Number of equality atoms :   33 ( 318 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f61,f85,f154,f158,f190,f192,f215])).

fof(f215,plain,
    ( ~ spl7_3
    | ~ spl7_5
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_5
    | spl7_11 ),
    inference(subsumption_resolution,[],[f213,f33])).

fof(f33,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ v2_compts_1(sK5,sK3)
      | ~ v2_compts_1(sK4,sK2) )
    & ( v2_compts_1(sK5,sK3)
      | v2_compts_1(sK4,sK2) )
    & sK4 = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_pre_topc(sK3,sK2)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) )
                    & ( v2_compts_1(X3,X1)
                      | v2_compts_1(X2,X0) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,sK2) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,sK2) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_pre_topc(X1,sK2) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v2_compts_1(X3,X1)
                  | ~ v2_compts_1(X2,sK2) )
                & ( v2_compts_1(X3,X1)
                  | v2_compts_1(X2,sK2) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_pre_topc(X1,sK2) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v2_compts_1(X3,sK3)
                | ~ v2_compts_1(X2,sK2) )
              & ( v2_compts_1(X3,sK3)
                | v2_compts_1(X2,sK2) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_pre_topc(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v2_compts_1(X3,sK3)
              | ~ v2_compts_1(X2,sK2) )
            & ( v2_compts_1(X3,sK3)
              | v2_compts_1(X2,sK2) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ? [X3] :
          ( ( ~ v2_compts_1(X3,sK3)
            | ~ v2_compts_1(sK4,sK2) )
          & ( v2_compts_1(X3,sK3)
            | v2_compts_1(sK4,sK2) )
          & sK4 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ( ~ v2_compts_1(X3,sK3)
          | ~ v2_compts_1(sK4,sK2) )
        & ( v2_compts_1(X3,sK3)
          | v2_compts_1(sK4,sK2) )
        & sK4 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ( ~ v2_compts_1(sK5,sK3)
        | ~ v2_compts_1(sK4,sK2) )
      & ( v2_compts_1(sK5,sK3)
        | v2_compts_1(sK4,sK2) )
      & sK4 = sK5
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( v2_compts_1(X2,X0)
                      <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).

fof(f213,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ spl7_3
    | ~ spl7_5
    | spl7_11 ),
    inference(subsumption_resolution,[],[f205,f187])).

fof(f187,plain,
    ( ~ sP0(sK3,sK4)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl7_11
  <=> sP0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f205,plain,
    ( sP0(sK3,sK4)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(resolution,[],[f157,f89])).

fof(f89,plain,
    ( r1_tarski(sK4,k2_struct_0(sK3))
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f88,f70])).

fof(f70,plain,
    ( l1_struct_0(sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl7_3
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f88,plain,
    ( r1_tarski(sK4,k2_struct_0(sK3))
    | ~ l1_struct_0(sK3) ),
    inference(superposition,[],[f80,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f80,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[],[f49,f63])).

fof(f63,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(forward_demodulation,[],[f35,f36])).

fof(f36,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f157,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK4,k2_struct_0(X1))
        | sP0(X1,sK4)
        | ~ m1_pre_topc(X1,sK2) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl7_5
  <=> ! [X1] :
        ( ~ r1_tarski(sK4,k2_struct_0(X1))
        | sP0(X1,sK4)
        | ~ m1_pre_topc(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f192,plain,
    ( ~ spl7_8
    | spl7_2 ),
    inference(avatar_split_clause,[],[f191,f57,f172])).

fof(f172,plain,
    ( spl7_8
  <=> v2_compts_1(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f57,plain,
    ( spl7_2
  <=> v2_compts_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f191,plain,
    ( ~ v2_compts_1(sK4,sK3)
    | spl7_2 ),
    inference(forward_demodulation,[],[f59,f36])).

fof(f59,plain,
    ( ~ v2_compts_1(sK5,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f190,plain,
    ( ~ spl7_11
    | spl7_8 ),
    inference(avatar_split_clause,[],[f106,f172,f185])).

fof(f106,plain,
    ( v2_compts_1(sK4,sK3)
    | ~ sP0(sK3,sK4) ),
    inference(resolution,[],[f51,f63])).

fof(f51,plain,(
    ! [X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X3,X0)
      | ~ sP0(X0,X3) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ v2_compts_1(sK6(X0,X1),X0)
          & sK6(X0,X1) = X1
          & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X0)
            | X1 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v2_compts_1(X2,X0)
          & X1 = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(sK6(X0,X1),X0)
        & sK6(X0,X1) = X1
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v2_compts_1(X2,X0)
            & X1 = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X0)
            | X1 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X2] :
      ( ( sP0(X1,X2)
        | ? [X3] :
            ( ~ v2_compts_1(X3,X1)
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X1)
            | X2 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X1,X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X1,X2] :
      ( sP0(X1,X2)
    <=> ! [X3] :
          ( v2_compts_1(X3,X1)
          | X2 != X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f158,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f143,f156,f53])).

fof(f53,plain,
    ( spl7_1
  <=> v2_compts_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f143,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK4,k2_struct_0(X1))
      | ~ m1_pre_topc(X1,sK2)
      | ~ v2_compts_1(sK4,sK2)
      | sP0(X1,sK4) ) ),
    inference(resolution,[],[f139,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v2_compts_1(X0,X2)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_compts_1(X0,X2)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_compts_1(X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ( ( v2_compts_1(X2,X0)
          | ~ sP0(X1,X2) )
        & ( sP0(X1,X2)
          | ~ v2_compts_1(X2,X0) ) )
      | ~ sP1(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ( v2_compts_1(X2,X0)
      <=> sP0(X1,X2) )
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f139,plain,(
    ! [X0] :
      ( sP1(sK4,X0,sK2)
      | ~ r1_tarski(sK4,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f133,f32])).

fof(f32,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,k2_struct_0(X0))
      | sP1(sK4,X0,sK2)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f48,f34])).

fof(f34,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | sP1(X2,X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X1,X0)
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f14,f16,f15])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

fof(f154,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f152,f62])).

fof(f62,plain,
    ( v2_compts_1(sK4,sK3)
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f58,f36])).

fof(f58,plain,
    ( v2_compts_1(sK5,sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f152,plain,
    ( ~ v2_compts_1(sK4,sK3)
    | spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f151,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ v2_compts_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(X1,X0)
      | sP0(X0,X1)
      | sP0(X0,X1) ) ),
    inference(superposition,[],[f47,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) = X1
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v2_compts_1(sK6(X0,X1),X0)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f151,plain,
    ( ~ sP0(sK3,sK4)
    | spl7_1
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f149,f33])).

fof(f149,plain,
    ( ~ m1_pre_topc(sK3,sK2)
    | ~ sP0(sK3,sK4)
    | spl7_1
    | ~ spl7_3 ),
    inference(resolution,[],[f144,f89])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK4,k2_struct_0(X0))
        | ~ m1_pre_topc(X0,sK2)
        | ~ sP0(X0,sK4) )
    | spl7_1 ),
    inference(subsumption_resolution,[],[f142,f55])).

fof(f55,plain,
    ( ~ v2_compts_1(sK4,sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f142,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK4,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK2)
      | ~ sP0(X0,sK4)
      | v2_compts_1(sK4,sK2) ) ),
    inference(resolution,[],[f139,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X0)
      | v2_compts_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f85,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f82,f69])).

fof(f82,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f78,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f78,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f77,f32])).

fof(f77,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f41,f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f61,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f37,f57,f53])).

fof(f37,plain,
    ( v2_compts_1(sK5,sK3)
    | v2_compts_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f38,f57,f53])).

fof(f38,plain,
    ( ~ v2_compts_1(sK5,sK3)
    | ~ v2_compts_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (8261)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.48  % (8261)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f60,f61,f85,f154,f158,f190,f192,f215])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    ~spl7_3 | ~spl7_5 | spl7_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f214])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    $false | (~spl7_3 | ~spl7_5 | spl7_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f213,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    m1_pre_topc(sK3,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ((((~v2_compts_1(sK5,sK3) | ~v2_compts_1(sK4,sK2)) & (v2_compts_1(sK5,sK3) | v2_compts_1(sK4,sK2)) & sK4 = sK5 & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(sK3,sK2)) & l1_pre_topc(sK2)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f19,f23,f22,f21,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,sK2)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(X1,sK2)) & l1_pre_topc(sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,sK2)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(X1,sK2)) => (? [X2] : (? [X3] : ((~v2_compts_1(X3,sK3) | ~v2_compts_1(X2,sK2)) & (v2_compts_1(X3,sK3) | v2_compts_1(X2,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_pre_topc(sK3,sK2))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ? [X2] : (? [X3] : ((~v2_compts_1(X3,sK3) | ~v2_compts_1(X2,sK2)) & (v2_compts_1(X3,sK3) | v2_compts_1(X2,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) => (? [X3] : ((~v2_compts_1(X3,sK3) | ~v2_compts_1(sK4,sK2)) & (v2_compts_1(X3,sK3) | v2_compts_1(sK4,sK2)) & sK4 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ? [X3] : ((~v2_compts_1(X3,sK3) | ~v2_compts_1(sK4,sK2)) & (v2_compts_1(X3,sK3) | v2_compts_1(sK4,sK2)) & sK4 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) => ((~v2_compts_1(sK5,sK3) | ~v2_compts_1(sK4,sK2)) & (v2_compts_1(sK5,sK3) | v2_compts_1(sK4,sK2)) & sK4 = sK5 & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    ~m1_pre_topc(sK3,sK2) | (~spl7_3 | ~spl7_5 | spl7_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f205,f187])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~sP0(sK3,sK4) | spl7_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f185])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    spl7_11 <=> sP0(sK3,sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    sP0(sK3,sK4) | ~m1_pre_topc(sK3,sK2) | (~spl7_3 | ~spl7_5)),
% 0.21/0.48    inference(resolution,[],[f157,f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    r1_tarski(sK4,k2_struct_0(sK3)) | ~spl7_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f88,f70])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    l1_struct_0(sK3) | ~spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl7_3 <=> l1_struct_0(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    r1_tarski(sK4,k2_struct_0(sK3)) | ~l1_struct_0(sK3)),
% 0.21/0.48    inference(superposition,[],[f80,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.48    inference(resolution,[],[f49,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.48    inference(forward_demodulation,[],[f35,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    sK4 = sK5),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(sK4,k2_struct_0(X1)) | sP0(X1,sK4) | ~m1_pre_topc(X1,sK2)) ) | ~spl7_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl7_5 <=> ! [X1] : (~r1_tarski(sK4,k2_struct_0(X1)) | sP0(X1,sK4) | ~m1_pre_topc(X1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ~spl7_8 | spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f191,f57,f172])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl7_8 <=> v2_compts_1(sK4,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl7_2 <=> v2_compts_1(sK5,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ~v2_compts_1(sK4,sK3) | spl7_2),
% 0.21/0.48    inference(forward_demodulation,[],[f59,f36])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ~v2_compts_1(sK5,sK3) | spl7_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ~spl7_11 | spl7_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f106,f172,f185])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    v2_compts_1(sK4,sK3) | ~sP0(sK3,sK4)),
% 0.21/0.48    inference(resolution,[],[f51,f63])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(X3,X0) | ~sP0(X0,X3)) )),
% 0.21/0.48    inference(equality_resolution,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP0(X0,X1) | (~v2_compts_1(sK6(X0,X1),X0) & sK6(X0,X1) = X1 & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (~v2_compts_1(X2,X0) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(sK6(X0,X1),X0) & sK6(X0,X1) = X1 & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v2_compts_1(X2,X0) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X1,X2] : ((sP0(X1,X2) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X1,X2)))),
% 0.21/0.48    inference(nnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X1,X2] : (sP0(X1,X2) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ~spl7_1 | spl7_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f143,f156,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl7_1 <=> v2_compts_1(sK4,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(sK4,k2_struct_0(X1)) | ~m1_pre_topc(X1,sK2) | ~v2_compts_1(sK4,sK2) | sP0(X1,sK4)) )),
% 0.21/0.48    inference(resolution,[],[f139,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v2_compts_1(X0,X2) | sP0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((v2_compts_1(X0,X2) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_compts_1(X0,X2))) | ~sP1(X0,X1,X2))),
% 0.21/0.48    inference(rectify,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (((v2_compts_1(X2,X0) | ~sP0(X1,X2)) & (sP0(X1,X2) | ~v2_compts_1(X2,X0))) | ~sP1(X2,X1,X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X2,X1,X0] : ((v2_compts_1(X2,X0) <=> sP0(X1,X2)) | ~sP1(X2,X1,X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ( ! [X0] : (sP1(sK4,X0,sK2) | ~r1_tarski(sK4,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK2)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    l1_pre_topc(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK4,k2_struct_0(X0)) | sP1(sK4,X0,sK2) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2)) )),
% 0.21/0.48    inference(resolution,[],[f48,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | sP1(X2,X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X1,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(definition_folding,[],[f14,f16,f15])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    spl7_1 | ~spl7_2 | ~spl7_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    $false | (spl7_1 | ~spl7_2 | ~spl7_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f152,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    v2_compts_1(sK4,sK3) | ~spl7_2),
% 0.21/0.48    inference(forward_demodulation,[],[f58,f36])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    v2_compts_1(sK5,sK3) | ~spl7_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    ~v2_compts_1(sK4,sK3) | (spl7_1 | ~spl7_3)),
% 0.21/0.48    inference(resolution,[],[f151,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP0(X0,X1) | ~v2_compts_1(X1,X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_compts_1(X1,X0) | sP0(X0,X1) | sP0(X0,X1)) )),
% 0.21/0.48    inference(superposition,[],[f47,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sK6(X0,X1) = X1 | sP0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_compts_1(sK6(X0,X1),X0) | sP0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~sP0(sK3,sK4) | (spl7_1 | ~spl7_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f33])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ~m1_pre_topc(sK3,sK2) | ~sP0(sK3,sK4) | (spl7_1 | ~spl7_3)),
% 0.21/0.48    inference(resolution,[],[f144,f89])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK4,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK2) | ~sP0(X0,sK4)) ) | spl7_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f142,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ~v2_compts_1(sK4,sK2) | spl7_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f53])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK4,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK2) | ~sP0(X0,sK4) | v2_compts_1(sK4,sK2)) )),
% 0.21/0.48    inference(resolution,[],[f139,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X0) | v2_compts_1(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f82,f69])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    l1_struct_0(sK3)),
% 0.21/0.48    inference(resolution,[],[f78,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    l1_pre_topc(sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f77,f32])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    l1_pre_topc(sK3) | ~l1_pre_topc(sK2)),
% 0.21/0.48    inference(resolution,[],[f41,f33])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl7_1 | spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f57,f53])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    v2_compts_1(sK5,sK3) | v2_compts_1(sK4,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ~spl7_1 | ~spl7_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f57,f53])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~v2_compts_1(sK5,sK3) | ~v2_compts_1(sK4,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (8261)------------------------------
% 0.21/0.48  % (8261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8261)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (8261)Memory used [KB]: 6140
% 0.21/0.48  % (8261)Time elapsed: 0.067 s
% 0.21/0.48  % (8261)------------------------------
% 0.21/0.48  % (8261)------------------------------
% 0.21/0.48  % (8253)Success in time 0.124 s
%------------------------------------------------------------------------------
