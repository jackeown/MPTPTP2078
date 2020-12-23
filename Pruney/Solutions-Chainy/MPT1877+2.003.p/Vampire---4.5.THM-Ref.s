%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:43 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 704 expanded)
%              Number of leaves         :   26 ( 256 expanded)
%              Depth                    :   26
%              Number of atoms          :  737 (4492 expanded)
%              Number of equality atoms :   83 ( 985 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f802,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f116,f137,f204,f207,f561,f571,f801])).

fof(f801,plain,
    ( ~ spl13_9
    | ~ spl13_10
    | spl13_12 ),
    inference(avatar_contradiction_clause,[],[f800])).

fof(f800,plain,
    ( $false
    | ~ spl13_9
    | ~ spl13_10
    | spl13_12 ),
    inference(subsumption_resolution,[],[f795,f133])).

fof(f133,plain,(
    sP3(sK8,sK6) ),
    inference(resolution,[],[f127,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | sP3(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ~ sP3(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP3(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP4(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ~ sP3(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP3(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP4(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
    <=> ( sP3(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f127,plain,(
    sP4(sK6,sK8) ),
    inference(subsumption_resolution,[],[f126,f55])).

fof(f55,plain,(
    v3_tex_2(sK8,sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v3_tex_2(sK9,sK7)
    & v3_tex_2(sK8,sK6)
    & sK8 = sK9
    & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7)))
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK7)
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f9,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_tex_2(X3,X1)
                    & v3_tex_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,sK6)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_tex_2(X3,X1)
                & v3_tex_2(X2,sK6)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_tex_2(X3,sK7)
              & v3_tex_2(X2,sK6)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v3_tex_2(X3,sK7)
            & v3_tex_2(X2,sK6)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ? [X3] :
          ( ~ v3_tex_2(X3,sK7)
          & v3_tex_2(sK8,sK6)
          & sK8 = X3
          & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7))) )
      & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ v3_tex_2(X3,sK7)
        & v3_tex_2(sK8,sK6)
        & sK8 = X3
        & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7))) )
   => ( ~ v3_tex_2(sK9,sK7)
      & v3_tex_2(sK8,sK6)
      & sK8 = sK9
      & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
      & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v3_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v3_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v3_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tex_2)).

fof(f126,plain,
    ( ~ v3_tex_2(sK8,sK6)
    | sP4(sK6,sK8) ),
    inference(resolution,[],[f123,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0,X1)
      | ~ v3_tex_2(X0,X1)
      | sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP4(X1,X0) )
        & ( sP4(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP5(X0,X1) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP4(X0,X1) )
        & ( sP4(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP5(X1,X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP4(X0,X1) )
      | ~ sP5(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f123,plain,(
    sP5(sK8,sK6) ),
    inference(subsumption_resolution,[],[f119,f49])).

fof(f49,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f29])).

fof(f119,plain,
    ( sP5(sK8,sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f81,f51])).

fof(f51,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP5(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP5(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f15,f23,f22,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( sP3(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f795,plain,
    ( ~ sP3(sK8,sK6)
    | ~ spl13_9
    | ~ spl13_10
    | spl13_12 ),
    inference(resolution,[],[f793,f570])).

fof(f570,plain,
    ( ~ sP3(sK8,sK7)
    | spl13_12 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl13_12
  <=> sP3(sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f793,plain,
    ( ! [X2] :
        ( sP3(X2,sK7)
        | ~ sP3(X2,sK6) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f792,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( sK12(X0,X1) != X0
      | sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ( sK12(X0,X1) != X0
          & r1_tarski(X0,sK12(X0,X1))
          & v2_tex_2(sK12(X0,X1),X1)
          & m1_subset_1(sK12(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP3(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK12(X0,X1) != X0
        & r1_tarski(X0,sK12(X0,X1))
        & v2_tex_2(sK12(X0,X1),X1)
        & m1_subset_1(sK12(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP3(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP3(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ( sP3(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP3(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f792,plain,
    ( ! [X2] :
        ( sK12(X2,sK7) = X2
        | ~ sP3(X2,sK6)
        | sP3(X2,sK7) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(duplicate_literal_removal,[],[f791])).

fof(f791,plain,
    ( ! [X2] :
        ( sK12(X2,sK7) = X2
        | ~ sP3(X2,sK6)
        | sP3(X2,sK7)
        | sP3(X2,sK7) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(resolution,[],[f651,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK12(X0,X1))
      | sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f651,plain,
    ( ! [X14,X13] :
        ( ~ r1_tarski(X13,sK12(X14,sK7))
        | sK12(X14,sK7) = X13
        | ~ sP3(X13,sK6)
        | sP3(X14,sK7) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f299,f511])).

fof(f511,plain,
    ( ! [X1] :
        ( v2_tex_2(sK12(X1,sK7),sK6)
        | sP3(X1,sK7) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f508,f291])).

fof(f291,plain,
    ( ! [X1] :
        ( sP1(sK7,sK12(X1,sK7))
        | sP3(X1,sK7) )
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f290,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK12(X0,X1),X1)
      | sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f290,plain,
    ( ! [X1] :
        ( sP3(X1,sK7)
        | ~ v2_tex_2(sK12(X1,sK7),sK7)
        | sP1(sK7,sK12(X1,sK7)) )
    | ~ spl13_10 ),
    inference(resolution,[],[f277,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v2_tex_2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f277,plain,
    ( ! [X1] :
        ( sP2(sK12(X1,sK7),sK7)
        | sP3(X1,sK7) )
    | ~ spl13_10 ),
    inference(resolution,[],[f226,f231])).

fof(f231,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK6)))
        | sP2(X9,sK7) )
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f225,f50])).

fof(f50,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f225,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK6)))
        | sP2(X9,sK7)
        | ~ l1_pre_topc(sK7) )
    | ~ spl13_10 ),
    inference(superposition,[],[f70,f209])).

fof(f209,plain,
    ( u1_struct_0(sK6) = u1_struct_0(sK7)
    | ~ spl13_10 ),
    inference(equality_resolution,[],[f203])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
        | u1_struct_0(sK7) = X0 )
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl13_10
  <=> ! [X1,X0] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
        | u1_struct_0(sK7) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f13,f19,f18,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( sP0(X2,X1,X0)
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f226,plain,
    ( ! [X10] :
        ( m1_subset_1(sK12(X10,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
        | sP3(X10,sK7) )
    | ~ spl13_10 ),
    inference(superposition,[],[f77,f209])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK12(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f508,plain,
    ( ! [X1] :
        ( ~ sP1(sK7,sK12(X1,sK7))
        | sP3(X1,sK7)
        | v2_tex_2(sK12(X1,sK7),sK6) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(resolution,[],[f506,f303])).

fof(f303,plain,
    ( ! [X0] :
        ( ~ sP1(sK6,sK12(X0,sK7))
        | sP3(X0,sK7)
        | v2_tex_2(sK12(X0,sK7),sK6) )
    | ~ spl13_10 ),
    inference(resolution,[],[f286,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f286,plain,
    ( ! [X7] :
        ( sP2(sK12(X7,sK7),sK6)
        | sP3(X7,sK7) )
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f282,f49])).

fof(f282,plain,
    ( ! [X7] :
        ( sP3(X7,sK7)
        | sP2(sK12(X7,sK7),sK6)
        | ~ l1_pre_topc(sK6) )
    | ~ spl13_10 ),
    inference(resolution,[],[f226,f70])).

fof(f506,plain,
    ( ! [X0] :
        ( sP1(sK6,X0)
        | ~ sP1(sK7,X0) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f505,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK10(X0,X1),X1)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ~ sP0(sK10(X0,X1),X1,X0)
          & r1_tarski(sK10(X0,X1),X1)
          & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP0(X2,X1,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP0(sK10(X0,X1),X1,X0)
        & r1_tarski(sK10(X0,X1),X1)
        & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( sP0(X2,X1,X0)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f505,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK10(sK6,X0),X0)
        | ~ sP1(sK7,X0)
        | sP1(sK6,X0) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(duplicate_literal_removal,[],[f504])).

fof(f504,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK10(sK6,X0),X0)
        | ~ sP1(sK7,X0)
        | sP1(sK6,X0)
        | sP1(sK6,X0) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(resolution,[],[f439,f501])).

fof(f501,plain,
    ( ! [X0] :
        ( ~ sP0(sK10(sK6,X0),X0,sK7)
        | sP1(sK6,X0) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(resolution,[],[f500,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK10(X0,X1),X1,X0)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f500,plain,
    ( ! [X0,X1] :
        ( sP0(X1,X0,sK6)
        | ~ sP0(X1,X0,sK7) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f412,f499])).

fof(f499,plain,
    ( ! [X10,X11] :
        ( v3_pre_topc(sK11(X10,X11,sK7),sK6)
        | ~ sP0(X10,X11,sK7) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f318,f329])).

fof(f329,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK11(X0,X1,sK7),u1_pre_topc(sK6))
        | ~ sP0(X0,X1,sK7) )
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f327,f50])).

fof(f327,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK11(X0,X1,sK7),u1_pre_topc(sK6))
        | ~ l1_pre_topc(sK7)
        | ~ sP0(X0,X1,sK7) )
    | ~ spl13_9 ),
    inference(superposition,[],[f166,f323])).

fof(f323,plain,
    ( u1_pre_topc(sK6) = u1_pre_topc(sK7)
    | ~ spl13_9 ),
    inference(equality_resolution,[],[f213])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
        | u1_pre_topc(sK7) = X1 )
    | ~ spl13_9 ),
    inference(subsumption_resolution,[],[f210,f199])).

fof(f199,plain,
    ( m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | ~ spl13_9 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl13_9
  <=> m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f210,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
      | u1_pre_topc(sK7) = X1
      | ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ) ),
    inference(superposition,[],[f83,f53])).

fof(f53,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f166,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK11(X2,X3,X4),u1_pre_topc(X4))
      | ~ l1_pre_topc(X4)
      | ~ sP0(X2,X3,X4) ) ),
    inference(subsumption_resolution,[],[f144,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK11(X0,X1,X2),X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( k9_subset_1(u1_struct_0(X2),X1,sK11(X0,X1,X2)) = X0
          & v3_pre_topc(sK11(X0,X1,X2),X2)
          & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k9_subset_1(u1_struct_0(X2),X1,sK11(X0,X1,X2)) = X0
        & v3_pre_topc(sK11(X0,X1,X2),X2)
        & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
            & v3_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
            & v3_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f144,plain,(
    ! [X4,X2,X3] :
      ( ~ v3_pre_topc(sK11(X2,X3,X4),X4)
      | r2_hidden(sK11(X2,X3,X4),u1_pre_topc(X4))
      | ~ l1_pre_topc(X4)
      | ~ sP0(X2,X3,X4) ) ),
    inference(resolution,[],[f58,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f318,plain,
    ( ! [X10,X11] :
        ( ~ sP0(X10,X11,sK7)
        | ~ r2_hidden(sK11(X10,X11,sK7),u1_pre_topc(sK6))
        | v3_pre_topc(sK11(X10,X11,sK7),sK6) )
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f314,f49])).

fof(f314,plain,
    ( ! [X10,X11] :
        ( ~ sP0(X10,X11,sK7)
        | ~ r2_hidden(sK11(X10,X11,sK7),u1_pre_topc(sK6))
        | v3_pre_topc(sK11(X10,X11,sK7),sK6)
        | ~ l1_pre_topc(sK6) )
    | ~ spl13_10 ),
    inference(resolution,[],[f223,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f223,plain,
    ( ! [X6,X5] :
        ( m1_subset_1(sK11(X5,X6,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ sP0(X5,X6,sK7) )
    | ~ spl13_10 ),
    inference(superposition,[],[f66,f209])).

fof(f412,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(sK11(X1,X0,sK7),sK6)
        | sP0(X1,X0,sK6)
        | ~ sP0(X1,X0,sK7) )
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f411,f223])).

fof(f411,plain,
    ( ! [X0,X1] :
        ( sP0(X1,X0,sK6)
        | ~ v3_pre_topc(sK11(X1,X0,sK7),sK6)
        | ~ m1_subset_1(sK11(X1,X0,sK7),k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ sP0(X1,X0,sK7) )
    | ~ spl13_10 ),
    inference(superposition,[],[f84,f224])).

fof(f224,plain,
    ( ! [X8,X7] :
        ( k9_subset_1(u1_struct_0(sK6),X7,sK11(X8,X7,sK7)) = X8
        | ~ sP0(X8,X7,sK7) )
    | ~ spl13_10 ),
    inference(superposition,[],[f68,f209])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(u1_struct_0(X2),X1,sK11(X0,X1,X2)) = X0
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    ! [X2,X3,X1] :
      ( sP0(k9_subset_1(u1_struct_0(X2),X1,X3),X1,X2)
      | ~ v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k9_subset_1(u1_struct_0(X2),X1,X3) != X0
      | ~ v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f439,plain,
    ( ! [X4,X3] :
        ( sP0(sK10(sK6,X3),X4,sK7)
        | ~ r1_tarski(sK10(sK6,X3),X4)
        | ~ sP1(sK7,X4)
        | sP1(sK6,X3) )
    | ~ spl13_10 ),
    inference(resolution,[],[f221,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK10(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f221,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ r1_tarski(X2,X3)
        | sP0(X2,X3,sK7)
        | ~ sP1(sK7,X3) )
    | ~ spl13_10 ),
    inference(superposition,[],[f62,f209])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X3,X1)
      | sP0(X3,X1,X0)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f299,plain,
    ( ! [X14,X13] :
        ( ~ r1_tarski(X13,sK12(X14,sK7))
        | ~ v2_tex_2(sK12(X14,sK7),sK6)
        | sK12(X14,sK7) = X13
        | ~ sP3(X13,sK6)
        | sP3(X14,sK7) )
    | ~ spl13_10 ),
    inference(resolution,[],[f76,f226])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X0,X3)
      | ~ v2_tex_2(X3,X1)
      | X0 = X3
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f571,plain,
    ( ~ spl13_3
    | ~ spl13_12 ),
    inference(avatar_split_clause,[],[f138,f568,f109])).

fof(f109,plain,
    ( spl13_3
  <=> v2_tex_2(sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f138,plain,
    ( ~ sP3(sK8,sK7)
    | ~ v2_tex_2(sK8,sK7) ),
    inference(resolution,[],[f130,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( sP4(X0,X1)
      | ~ sP3(X1,X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f130,plain,(
    ~ sP4(sK7,sK8) ),
    inference(subsumption_resolution,[],[f128,f85])).

fof(f85,plain,(
    ~ v3_tex_2(sK8,sK7) ),
    inference(forward_demodulation,[],[f56,f54])).

fof(f54,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ~ v3_tex_2(sK9,sK7) ),
    inference(cnf_transformation,[],[f29])).

fof(f128,plain,
    ( ~ sP4(sK7,sK8)
    | v3_tex_2(sK8,sK7) ),
    inference(resolution,[],[f124,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0,X1)
      | ~ sP4(X1,X0)
      | v3_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f124,plain,(
    sP5(sK8,sK7) ),
    inference(subsumption_resolution,[],[f120,f50])).

fof(f120,plain,
    ( sP5(sK8,sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(resolution,[],[f81,f86])).

fof(f86,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(forward_demodulation,[],[f52,f54])).

fof(f52,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7))) ),
    inference(cnf_transformation,[],[f29])).

fof(f561,plain,
    ( ~ spl13_2
    | spl13_4
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(avatar_contradiction_clause,[],[f560])).

fof(f560,plain,
    ( $false
    | ~ spl13_2
    | spl13_4
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f550,f102])).

fof(f102,plain,
    ( sP1(sK6,sK8)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl13_2
  <=> sP1(sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f550,plain,
    ( ~ sP1(sK6,sK8)
    | spl13_4
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(resolution,[],[f549,f115])).

fof(f115,plain,
    ( ~ sP1(sK7,sK8)
    | spl13_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl13_4
  <=> sP1(sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f549,plain,
    ( ! [X0] :
        ( sP1(sK7,X0)
        | ~ sP1(sK6,X0) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f548,f64])).

fof(f548,plain,
    ( ! [X0] :
        ( sP1(sK7,X0)
        | ~ r1_tarski(sK10(sK7,X0),X0)
        | ~ sP1(sK6,X0) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(duplicate_literal_removal,[],[f546])).

fof(f546,plain,
    ( ! [X0] :
        ( sP1(sK7,X0)
        | ~ r1_tarski(sK10(sK7,X0),X0)
        | sP1(sK7,X0)
        | ~ sP1(sK6,X0) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(resolution,[],[f544,f257])).

fof(f257,plain,
    ( ! [X2,X3] :
        ( sP0(sK10(sK7,X2),X3,sK6)
        | ~ r1_tarski(sK10(sK7,X2),X3)
        | sP1(sK7,X2)
        | ~ sP1(sK6,X3) )
    | ~ spl13_10 ),
    inference(resolution,[],[f222,f62])).

fof(f222,plain,
    ( ! [X4] :
        ( m1_subset_1(sK10(sK7,X4),k1_zfmisc_1(u1_struct_0(sK6)))
        | sP1(sK7,X4) )
    | ~ spl13_10 ),
    inference(superposition,[],[f63,f209])).

fof(f544,plain,
    ( ! [X0] :
        ( ~ sP0(sK10(sK7,X0),X0,sK6)
        | sP1(sK7,X0) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(resolution,[],[f537,f65])).

fof(f537,plain,
    ( ! [X0,X1] :
        ( sP0(X1,X0,sK7)
        | ~ sP0(X1,X0,sK6) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f467,f535])).

fof(f535,plain,
    ( ! [X2,X3] :
        ( v3_pre_topc(sK11(X2,X3,sK6),sK7)
        | ~ sP0(X2,X3,sK6) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f533,f49])).

fof(f533,plain,
    ( ! [X2,X3] :
        ( v3_pre_topc(sK11(X2,X3,sK6),sK7)
        | ~ sP0(X2,X3,sK6)
        | ~ l1_pre_topc(sK6) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(duplicate_literal_removal,[],[f532])).

fof(f532,plain,
    ( ! [X2,X3] :
        ( v3_pre_topc(sK11(X2,X3,sK6),sK7)
        | ~ sP0(X2,X3,sK6)
        | ~ l1_pre_topc(sK6)
        | ~ sP0(X2,X3,sK6) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(resolution,[],[f356,f166])).

fof(f356,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(sK11(X4,X5,sK6),u1_pre_topc(sK6))
        | v3_pre_topc(sK11(X4,X5,sK6),sK7)
        | ~ sP0(X4,X5,sK6) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(resolution,[],[f342,f66])).

fof(f342,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ r2_hidden(X1,u1_pre_topc(sK6))
        | v3_pre_topc(X1,sK7) )
    | ~ spl13_9
    | ~ spl13_10 ),
    inference(forward_demodulation,[],[f230,f323])).

fof(f230,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ r2_hidden(X1,u1_pre_topc(sK7))
        | v3_pre_topc(X1,sK7) )
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f220,f50])).

fof(f220,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ r2_hidden(X1,u1_pre_topc(sK7))
        | v3_pre_topc(X1,sK7)
        | ~ l1_pre_topc(sK7) )
    | ~ spl13_10 ),
    inference(superposition,[],[f59,f209])).

fof(f467,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(sK11(X1,X0,sK6),sK7)
        | sP0(X1,X0,sK7)
        | ~ sP0(X1,X0,sK6) )
    | ~ spl13_10 ),
    inference(subsumption_resolution,[],[f465,f66])).

fof(f465,plain,
    ( ! [X0,X1] :
        ( sP0(X1,X0,sK7)
        | ~ v3_pre_topc(sK11(X1,X0,sK6),sK7)
        | ~ m1_subset_1(sK11(X1,X0,sK6),k1_zfmisc_1(u1_struct_0(sK6)))
        | ~ sP0(X1,X0,sK6) )
    | ~ spl13_10 ),
    inference(superposition,[],[f270,f68])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( sP0(k9_subset_1(u1_struct_0(sK6),X0,X1),X0,sK7)
        | ~ v3_pre_topc(X1,sK7)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
    | ~ spl13_10 ),
    inference(superposition,[],[f84,f209])).

fof(f207,plain,(
    spl13_9 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl13_9 ),
    inference(subsumption_resolution,[],[f205,f50])).

fof(f205,plain,
    ( ~ l1_pre_topc(sK7)
    | spl13_9 ),
    inference(resolution,[],[f200,f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f200,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    | spl13_9 ),
    inference(avatar_component_clause,[],[f198])).

fof(f204,plain,
    ( ~ spl13_9
    | spl13_10 ),
    inference(avatar_split_clause,[],[f194,f202,f198])).

fof(f194,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
      | u1_struct_0(sK7) = X0
      | ~ m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ) ),
    inference(superposition,[],[f82,f53])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f137,plain,(
    spl13_1 ),
    inference(avatar_split_clause,[],[f134,f97])).

fof(f97,plain,
    ( spl13_1
  <=> v2_tex_2(sK8,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f134,plain,(
    v2_tex_2(sK8,sK6) ),
    inference(resolution,[],[f127,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f116,plain,
    ( spl13_3
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f106,f113,f109])).

fof(f106,plain,
    ( ~ sP1(sK7,sK8)
    | v2_tex_2(sK8,sK7) ),
    inference(resolution,[],[f93,f61])).

fof(f93,plain,(
    sP2(sK8,sK7) ),
    inference(subsumption_resolution,[],[f90,f50])).

fof(f90,plain,
    ( sP2(sK8,sK7)
    | ~ l1_pre_topc(sK7) ),
    inference(resolution,[],[f70,f86])).

fof(f105,plain,
    ( spl13_2
    | ~ spl13_1 ),
    inference(avatar_split_clause,[],[f95,f97,f101])).

fof(f95,plain,
    ( ~ v2_tex_2(sK8,sK6)
    | sP1(sK6,sK8) ),
    inference(resolution,[],[f92,f60])).

fof(f92,plain,(
    sP2(sK8,sK6) ),
    inference(subsumption_resolution,[],[f89,f49])).

fof(f89,plain,
    ( sP2(sK8,sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f70,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (1167)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (1158)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (1164)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (1171)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (1158)Refutation not found, incomplete strategy% (1158)------------------------------
% 0.21/0.50  % (1158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1158)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1158)Memory used [KB]: 10618
% 0.21/0.50  % (1158)Time elapsed: 0.096 s
% 0.21/0.50  % (1158)------------------------------
% 0.21/0.50  % (1158)------------------------------
% 0.21/0.50  % (1162)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (1159)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (1161)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (1170)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (1174)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (1181)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (1173)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (1177)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (1165)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (1172)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (1169)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (1183)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (1166)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (1179)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (1166)Refutation not found, incomplete strategy% (1166)------------------------------
% 0.21/0.52  % (1166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1166)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1166)Memory used [KB]: 1663
% 0.21/0.52  % (1166)Time elapsed: 0.078 s
% 0.21/0.52  % (1166)------------------------------
% 0.21/0.52  % (1166)------------------------------
% 0.21/0.52  % (1163)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (1182)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (1180)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (1175)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (1178)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (1176)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (1168)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (1184)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.56/0.56  % (1163)Refutation found. Thanks to Tanya!
% 1.56/0.56  % SZS status Theorem for theBenchmark
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f802,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(avatar_sat_refutation,[],[f105,f116,f137,f204,f207,f561,f571,f801])).
% 1.56/0.57  fof(f801,plain,(
% 1.56/0.57    ~spl13_9 | ~spl13_10 | spl13_12),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f800])).
% 1.56/0.57  fof(f800,plain,(
% 1.56/0.57    $false | (~spl13_9 | ~spl13_10 | spl13_12)),
% 1.56/0.57    inference(subsumption_resolution,[],[f795,f133])).
% 1.56/0.57  fof(f133,plain,(
% 1.56/0.57    sP3(sK8,sK6)),
% 1.56/0.57    inference(resolution,[],[f127,f74])).
% 1.56/0.57  fof(f74,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~sP4(X0,X1) | sP3(X1,X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f44])).
% 1.56/0.57  fof(f44,plain,(
% 1.56/0.57    ! [X0,X1] : ((sP4(X0,X1) | ~sP3(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP3(X1,X0) & v2_tex_2(X1,X0)) | ~sP4(X0,X1)))),
% 1.56/0.57    inference(flattening,[],[f43])).
% 1.56/0.57  fof(f43,plain,(
% 1.56/0.57    ! [X0,X1] : ((sP4(X0,X1) | (~sP3(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP3(X1,X0) & v2_tex_2(X1,X0)) | ~sP4(X0,X1)))),
% 1.56/0.57    inference(nnf_transformation,[],[f22])).
% 1.56/0.57  fof(f22,plain,(
% 1.56/0.57    ! [X0,X1] : (sP4(X0,X1) <=> (sP3(X1,X0) & v2_tex_2(X1,X0)))),
% 1.56/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.56/0.57  fof(f127,plain,(
% 1.56/0.57    sP4(sK6,sK8)),
% 1.56/0.57    inference(subsumption_resolution,[],[f126,f55])).
% 1.56/0.57  fof(f55,plain,(
% 1.56/0.57    v3_tex_2(sK8,sK6)),
% 1.56/0.57    inference(cnf_transformation,[],[f29])).
% 1.56/0.57  fof(f29,plain,(
% 1.56/0.57    (((~v3_tex_2(sK9,sK7) & v3_tex_2(sK8,sK6) & sK8 = sK9 & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7)))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK7)) & l1_pre_topc(sK6)),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f9,f28,f27,f26,f25])).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,sK6) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(X1)) & l1_pre_topc(sK6))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,sK6) & X2 = X3 & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v3_tex_2(X3,sK7) & v3_tex_2(X2,sK6) & X2 = X3 & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK7))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ? [X2] : (? [X3] : (~v3_tex_2(X3,sK7) & v3_tex_2(X2,sK6) & X2 = X3 & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) => (? [X3] : (~v3_tex_2(X3,sK7) & v3_tex_2(sK8,sK6) & sK8 = X3 & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ? [X3] : (~v3_tex_2(X3,sK7) & v3_tex_2(sK8,sK6) & sK8 = X3 & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK7)))) => (~v3_tex_2(sK9,sK7) & v3_tex_2(sK8,sK6) & sK8 = sK9 & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7))))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f9,plain,(
% 1.56/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.56/0.57    inference(flattening,[],[f8])).
% 1.73/0.57  fof(f8,plain,(
% 1.73/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v3_tex_2(X3,X1) & (v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 1.73/0.57    inference(ennf_transformation,[],[f7])).
% 1.73/0.57  fof(f7,negated_conjecture,(
% 1.73/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tex_2(X3,X1))))))),
% 1.73/0.57    inference(negated_conjecture,[],[f6])).
% 1.73/0.57  fof(f6,conjecture,(
% 1.73/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tex_2(X3,X1))))))),
% 1.73/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_tex_2)).
% 1.73/0.57  fof(f126,plain,(
% 1.73/0.57    ~v3_tex_2(sK8,sK6) | sP4(sK6,sK8)),
% 1.73/0.57    inference(resolution,[],[f123,f71])).
% 1.73/0.57  fof(f71,plain,(
% 1.73/0.57    ( ! [X0,X1] : (~sP5(X0,X1) | ~v3_tex_2(X0,X1) | sP4(X1,X0)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f42])).
% 1.73/0.57  fof(f42,plain,(
% 1.73/0.57    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP4(X1,X0)) & (sP4(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP5(X0,X1))),
% 1.73/0.57    inference(rectify,[],[f41])).
% 1.73/0.57  fof(f41,plain,(
% 1.73/0.57    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP4(X0,X1)) & (sP4(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP5(X1,X0))),
% 1.73/0.57    inference(nnf_transformation,[],[f23])).
% 1.73/0.57  fof(f23,plain,(
% 1.73/0.57    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP4(X0,X1)) | ~sP5(X1,X0))),
% 1.73/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 1.73/0.57  fof(f123,plain,(
% 1.73/0.57    sP5(sK8,sK6)),
% 1.73/0.57    inference(subsumption_resolution,[],[f119,f49])).
% 1.73/0.57  fof(f49,plain,(
% 1.73/0.57    l1_pre_topc(sK6)),
% 1.73/0.57    inference(cnf_transformation,[],[f29])).
% 1.73/0.57  fof(f119,plain,(
% 1.73/0.57    sP5(sK8,sK6) | ~l1_pre_topc(sK6)),
% 1.73/0.57    inference(resolution,[],[f81,f51])).
% 1.73/0.57  fof(f51,plain,(
% 1.73/0.57    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))),
% 1.73/0.57    inference(cnf_transformation,[],[f29])).
% 1.73/0.57  fof(f81,plain,(
% 1.73/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP5(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f24])).
% 1.73/0.57  fof(f24,plain,(
% 1.73/0.57    ! [X0] : (! [X1] : (sP5(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.57    inference(definition_folding,[],[f15,f23,f22,f21])).
% 1.73/0.57  fof(f21,plain,(
% 1.73/0.57    ! [X1,X0] : (sP3(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.73/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.73/0.57  fof(f15,plain,(
% 1.73/0.57    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.57    inference(flattening,[],[f14])).
% 1.73/0.57  fof(f14,plain,(
% 1.73/0.57    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.57    inference(ennf_transformation,[],[f5])).
% 1.73/0.57  fof(f5,axiom,(
% 1.73/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.73/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 1.73/0.57  fof(f795,plain,(
% 1.73/0.57    ~sP3(sK8,sK6) | (~spl13_9 | ~spl13_10 | spl13_12)),
% 1.73/0.57    inference(resolution,[],[f793,f570])).
% 1.73/0.57  fof(f570,plain,(
% 1.73/0.57    ~sP3(sK8,sK7) | spl13_12),
% 1.73/0.57    inference(avatar_component_clause,[],[f568])).
% 1.73/0.57  fof(f568,plain,(
% 1.73/0.57    spl13_12 <=> sP3(sK8,sK7)),
% 1.73/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).
% 1.73/0.57  fof(f793,plain,(
% 1.73/0.57    ( ! [X2] : (sP3(X2,sK7) | ~sP3(X2,sK6)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(subsumption_resolution,[],[f792,f80])).
% 1.73/0.57  fof(f80,plain,(
% 1.73/0.57    ( ! [X0,X1] : (sK12(X0,X1) != X0 | sP3(X0,X1)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f48])).
% 1.73/0.57  fof(f48,plain,(
% 1.73/0.57    ! [X0,X1] : ((sP3(X0,X1) | (sK12(X0,X1) != X0 & r1_tarski(X0,sK12(X0,X1)) & v2_tex_2(sK12(X0,X1),X1) & m1_subset_1(sK12(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP3(X0,X1)))),
% 1.73/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f46,f47])).
% 1.73/0.57  fof(f47,plain,(
% 1.73/0.57    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK12(X0,X1) != X0 & r1_tarski(X0,sK12(X0,X1)) & v2_tex_2(sK12(X0,X1),X1) & m1_subset_1(sK12(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.73/0.57    introduced(choice_axiom,[])).
% 1.73/0.57  fof(f46,plain,(
% 1.73/0.57    ! [X0,X1] : ((sP3(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP3(X0,X1)))),
% 1.73/0.57    inference(rectify,[],[f45])).
% 1.73/0.57  fof(f45,plain,(
% 1.73/0.57    ! [X1,X0] : ((sP3(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X1,X0)))),
% 1.73/0.57    inference(nnf_transformation,[],[f21])).
% 1.73/0.57  fof(f792,plain,(
% 1.73/0.57    ( ! [X2] : (sK12(X2,sK7) = X2 | ~sP3(X2,sK6) | sP3(X2,sK7)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(duplicate_literal_removal,[],[f791])).
% 1.73/0.57  fof(f791,plain,(
% 1.73/0.57    ( ! [X2] : (sK12(X2,sK7) = X2 | ~sP3(X2,sK6) | sP3(X2,sK7) | sP3(X2,sK7)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(resolution,[],[f651,f79])).
% 1.73/0.57  fof(f79,plain,(
% 1.73/0.57    ( ! [X0,X1] : (r1_tarski(X0,sK12(X0,X1)) | sP3(X0,X1)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f48])).
% 1.73/0.57  fof(f651,plain,(
% 1.73/0.57    ( ! [X14,X13] : (~r1_tarski(X13,sK12(X14,sK7)) | sK12(X14,sK7) = X13 | ~sP3(X13,sK6) | sP3(X14,sK7)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(subsumption_resolution,[],[f299,f511])).
% 1.73/0.57  fof(f511,plain,(
% 1.73/0.57    ( ! [X1] : (v2_tex_2(sK12(X1,sK7),sK6) | sP3(X1,sK7)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(subsumption_resolution,[],[f508,f291])).
% 1.73/0.57  fof(f291,plain,(
% 1.73/0.57    ( ! [X1] : (sP1(sK7,sK12(X1,sK7)) | sP3(X1,sK7)) ) | ~spl13_10),
% 1.73/0.57    inference(subsumption_resolution,[],[f290,f78])).
% 1.73/0.57  fof(f78,plain,(
% 1.73/0.57    ( ! [X0,X1] : (v2_tex_2(sK12(X0,X1),X1) | sP3(X0,X1)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f48])).
% 1.73/0.57  fof(f290,plain,(
% 1.73/0.57    ( ! [X1] : (sP3(X1,sK7) | ~v2_tex_2(sK12(X1,sK7),sK7) | sP1(sK7,sK12(X1,sK7))) ) | ~spl13_10),
% 1.73/0.57    inference(resolution,[],[f277,f60])).
% 1.73/0.57  fof(f60,plain,(
% 1.73/0.57    ( ! [X0,X1] : (~sP2(X0,X1) | ~v2_tex_2(X0,X1) | sP1(X1,X0)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f32])).
% 1.73/0.57  fof(f32,plain,(
% 1.73/0.57    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 1.73/0.57    inference(rectify,[],[f31])).
% 1.73/0.57  fof(f31,plain,(
% 1.73/0.57    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 1.73/0.57    inference(nnf_transformation,[],[f19])).
% 1.73/0.57  fof(f19,plain,(
% 1.73/0.57    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 1.73/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.73/0.57  fof(f277,plain,(
% 1.73/0.57    ( ! [X1] : (sP2(sK12(X1,sK7),sK7) | sP3(X1,sK7)) ) | ~spl13_10),
% 1.73/0.57    inference(resolution,[],[f226,f231])).
% 1.73/0.57  fof(f231,plain,(
% 1.73/0.57    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK6))) | sP2(X9,sK7)) ) | ~spl13_10),
% 1.73/0.57    inference(subsumption_resolution,[],[f225,f50])).
% 1.73/0.57  fof(f50,plain,(
% 1.73/0.57    l1_pre_topc(sK7)),
% 1.73/0.57    inference(cnf_transformation,[],[f29])).
% 1.73/0.57  fof(f225,plain,(
% 1.73/0.57    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK6))) | sP2(X9,sK7) | ~l1_pre_topc(sK7)) ) | ~spl13_10),
% 1.73/0.57    inference(superposition,[],[f70,f209])).
% 1.73/0.57  fof(f209,plain,(
% 1.73/0.57    u1_struct_0(sK6) = u1_struct_0(sK7) | ~spl13_10),
% 1.73/0.57    inference(equality_resolution,[],[f203])).
% 1.73/0.57  fof(f203,plain,(
% 1.73/0.57    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) | u1_struct_0(sK7) = X0) ) | ~spl13_10),
% 1.73/0.57    inference(avatar_component_clause,[],[f202])).
% 1.73/0.57  fof(f202,plain,(
% 1.73/0.57    spl13_10 <=> ! [X1,X0] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) | u1_struct_0(sK7) = X0)),
% 1.73/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).
% 1.73/0.57  fof(f70,plain,(
% 1.73/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f20])).
% 1.73/0.57  fof(f20,plain,(
% 1.73/0.57    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.57    inference(definition_folding,[],[f13,f19,f18,f17])).
% 1.73/0.57  fof(f17,plain,(
% 1.73/0.57    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.73/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.73/0.57  fof(f18,plain,(
% 1.73/0.57    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.73/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.73/0.57  fof(f13,plain,(
% 1.73/0.57    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.57    inference(flattening,[],[f12])).
% 1.73/0.57  fof(f12,plain,(
% 1.73/0.57    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.57    inference(ennf_transformation,[],[f4])).
% 1.73/0.57  fof(f4,axiom,(
% 1.73/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 1.73/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 1.73/0.57  fof(f226,plain,(
% 1.73/0.57    ( ! [X10] : (m1_subset_1(sK12(X10,sK7),k1_zfmisc_1(u1_struct_0(sK6))) | sP3(X10,sK7)) ) | ~spl13_10),
% 1.73/0.57    inference(superposition,[],[f77,f209])).
% 1.73/0.57  fof(f77,plain,(
% 1.73/0.57    ( ! [X0,X1] : (m1_subset_1(sK12(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP3(X0,X1)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f48])).
% 1.73/0.57  fof(f508,plain,(
% 1.73/0.57    ( ! [X1] : (~sP1(sK7,sK12(X1,sK7)) | sP3(X1,sK7) | v2_tex_2(sK12(X1,sK7),sK6)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(resolution,[],[f506,f303])).
% 1.73/0.57  fof(f303,plain,(
% 1.73/0.57    ( ! [X0] : (~sP1(sK6,sK12(X0,sK7)) | sP3(X0,sK7) | v2_tex_2(sK12(X0,sK7),sK6)) ) | ~spl13_10),
% 1.73/0.57    inference(resolution,[],[f286,f61])).
% 1.73/0.57  fof(f61,plain,(
% 1.73/0.57    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v2_tex_2(X0,X1)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f32])).
% 1.73/0.57  fof(f286,plain,(
% 1.73/0.57    ( ! [X7] : (sP2(sK12(X7,sK7),sK6) | sP3(X7,sK7)) ) | ~spl13_10),
% 1.73/0.57    inference(subsumption_resolution,[],[f282,f49])).
% 1.73/0.57  fof(f282,plain,(
% 1.73/0.57    ( ! [X7] : (sP3(X7,sK7) | sP2(sK12(X7,sK7),sK6) | ~l1_pre_topc(sK6)) ) | ~spl13_10),
% 1.73/0.57    inference(resolution,[],[f226,f70])).
% 1.73/0.57  fof(f506,plain,(
% 1.73/0.57    ( ! [X0] : (sP1(sK6,X0) | ~sP1(sK7,X0)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(subsumption_resolution,[],[f505,f64])).
% 1.73/0.57  fof(f64,plain,(
% 1.73/0.57    ( ! [X0,X1] : (r1_tarski(sK10(X0,X1),X1) | sP1(X0,X1)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f36])).
% 1.73/0.57  fof(f36,plain,(
% 1.73/0.57    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(sK10(X0,X1),X1,X0) & r1_tarski(sK10(X0,X1),X1) & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 1.73/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f34,f35])).
% 1.73/0.57  fof(f35,plain,(
% 1.73/0.57    ! [X1,X0] : (? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP0(sK10(X0,X1),X1,X0) & r1_tarski(sK10(X0,X1),X1) & m1_subset_1(sK10(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.73/0.57    introduced(choice_axiom,[])).
% 1.73/0.57  fof(f34,plain,(
% 1.73/0.57    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 1.73/0.57    inference(rectify,[],[f33])).
% 1.73/0.57  fof(f33,plain,(
% 1.73/0.57    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 1.73/0.57    inference(nnf_transformation,[],[f18])).
% 1.73/0.57  fof(f505,plain,(
% 1.73/0.57    ( ! [X0] : (~r1_tarski(sK10(sK6,X0),X0) | ~sP1(sK7,X0) | sP1(sK6,X0)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(duplicate_literal_removal,[],[f504])).
% 1.73/0.57  fof(f504,plain,(
% 1.73/0.57    ( ! [X0] : (~r1_tarski(sK10(sK6,X0),X0) | ~sP1(sK7,X0) | sP1(sK6,X0) | sP1(sK6,X0)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(resolution,[],[f439,f501])).
% 1.73/0.57  fof(f501,plain,(
% 1.73/0.57    ( ! [X0] : (~sP0(sK10(sK6,X0),X0,sK7) | sP1(sK6,X0)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(resolution,[],[f500,f65])).
% 1.73/0.57  fof(f65,plain,(
% 1.73/0.57    ( ! [X0,X1] : (~sP0(sK10(X0,X1),X1,X0) | sP1(X0,X1)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f36])).
% 1.73/0.57  fof(f500,plain,(
% 1.73/0.57    ( ! [X0,X1] : (sP0(X1,X0,sK6) | ~sP0(X1,X0,sK7)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(subsumption_resolution,[],[f412,f499])).
% 1.73/0.57  fof(f499,plain,(
% 1.73/0.57    ( ! [X10,X11] : (v3_pre_topc(sK11(X10,X11,sK7),sK6) | ~sP0(X10,X11,sK7)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(subsumption_resolution,[],[f318,f329])).
% 1.73/0.57  fof(f329,plain,(
% 1.73/0.57    ( ! [X0,X1] : (r2_hidden(sK11(X0,X1,sK7),u1_pre_topc(sK6)) | ~sP0(X0,X1,sK7)) ) | ~spl13_9),
% 1.73/0.57    inference(subsumption_resolution,[],[f327,f50])).
% 1.73/0.57  fof(f327,plain,(
% 1.73/0.57    ( ! [X0,X1] : (r2_hidden(sK11(X0,X1,sK7),u1_pre_topc(sK6)) | ~l1_pre_topc(sK7) | ~sP0(X0,X1,sK7)) ) | ~spl13_9),
% 1.73/0.57    inference(superposition,[],[f166,f323])).
% 1.73/0.57  fof(f323,plain,(
% 1.73/0.57    u1_pre_topc(sK6) = u1_pre_topc(sK7) | ~spl13_9),
% 1.73/0.57    inference(equality_resolution,[],[f213])).
% 1.73/0.57  fof(f213,plain,(
% 1.73/0.57    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) | u1_pre_topc(sK7) = X1) ) | ~spl13_9),
% 1.73/0.57    inference(subsumption_resolution,[],[f210,f199])).
% 1.73/0.57  fof(f199,plain,(
% 1.73/0.57    m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) | ~spl13_9),
% 1.73/0.57    inference(avatar_component_clause,[],[f198])).
% 1.73/0.57  fof(f198,plain,(
% 1.73/0.57    spl13_9 <=> m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))),
% 1.73/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 1.73/0.57  fof(f210,plain,(
% 1.73/0.57    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) | u1_pre_topc(sK7) = X1 | ~m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))) )),
% 1.73/0.57    inference(superposition,[],[f83,f53])).
% 1.73/0.57  fof(f53,plain,(
% 1.73/0.57    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))),
% 1.73/0.57    inference(cnf_transformation,[],[f29])).
% 1.73/0.57  fof(f83,plain,(
% 1.73/0.57    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X1 = X3 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.73/0.57    inference(cnf_transformation,[],[f16])).
% 1.73/0.57  fof(f16,plain,(
% 1.73/0.57    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.73/0.57    inference(ennf_transformation,[],[f3])).
% 1.73/0.57  fof(f3,axiom,(
% 1.73/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.73/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 1.73/0.57  fof(f166,plain,(
% 1.73/0.57    ( ! [X4,X2,X3] : (r2_hidden(sK11(X2,X3,X4),u1_pre_topc(X4)) | ~l1_pre_topc(X4) | ~sP0(X2,X3,X4)) )),
% 1.73/0.57    inference(subsumption_resolution,[],[f144,f67])).
% 1.73/0.57  fof(f67,plain,(
% 1.73/0.57    ( ! [X2,X0,X1] : (v3_pre_topc(sK11(X0,X1,X2),X2) | ~sP0(X0,X1,X2)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f40])).
% 1.73/0.57  fof(f40,plain,(
% 1.73/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((k9_subset_1(u1_struct_0(X2),X1,sK11(X0,X1,X2)) = X0 & v3_pre_topc(sK11(X0,X1,X2),X2) & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 1.73/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f38,f39])).
% 1.73/0.57  fof(f39,plain,(
% 1.73/0.57    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (k9_subset_1(u1_struct_0(X2),X1,sK11(X0,X1,X2)) = X0 & v3_pre_topc(sK11(X0,X1,X2),X2) & m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 1.73/0.57    introduced(choice_axiom,[])).
% 1.73/0.57  fof(f38,plain,(
% 1.73/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 1.73/0.57    inference(rectify,[],[f37])).
% 1.73/0.57  fof(f37,plain,(
% 1.73/0.57    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X2,X1,X0)))),
% 1.73/0.57    inference(nnf_transformation,[],[f17])).
% 1.73/0.57  fof(f144,plain,(
% 1.73/0.57    ( ! [X4,X2,X3] : (~v3_pre_topc(sK11(X2,X3,X4),X4) | r2_hidden(sK11(X2,X3,X4),u1_pre_topc(X4)) | ~l1_pre_topc(X4) | ~sP0(X2,X3,X4)) )),
% 1.73/0.57    inference(resolution,[],[f58,f66])).
% 1.73/0.57  fof(f66,plain,(
% 1.73/0.57    ( ! [X2,X0,X1] : (m1_subset_1(sK11(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f40])).
% 1.73/0.57  fof(f58,plain,(
% 1.73/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f30])).
% 1.73/0.57  fof(f30,plain,(
% 1.73/0.57    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.57    inference(nnf_transformation,[],[f11])).
% 1.73/0.57  fof(f11,plain,(
% 1.73/0.57    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.57    inference(ennf_transformation,[],[f1])).
% 1.73/0.57  fof(f1,axiom,(
% 1.73/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.73/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.73/0.57  fof(f318,plain,(
% 1.73/0.57    ( ! [X10,X11] : (~sP0(X10,X11,sK7) | ~r2_hidden(sK11(X10,X11,sK7),u1_pre_topc(sK6)) | v3_pre_topc(sK11(X10,X11,sK7),sK6)) ) | ~spl13_10),
% 1.73/0.57    inference(subsumption_resolution,[],[f314,f49])).
% 1.73/0.57  fof(f314,plain,(
% 1.73/0.57    ( ! [X10,X11] : (~sP0(X10,X11,sK7) | ~r2_hidden(sK11(X10,X11,sK7),u1_pre_topc(sK6)) | v3_pre_topc(sK11(X10,X11,sK7),sK6) | ~l1_pre_topc(sK6)) ) | ~spl13_10),
% 1.73/0.57    inference(resolution,[],[f223,f59])).
% 1.73/0.57  fof(f59,plain,(
% 1.73/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f30])).
% 1.73/0.57  fof(f223,plain,(
% 1.73/0.57    ( ! [X6,X5] : (m1_subset_1(sK11(X5,X6,sK7),k1_zfmisc_1(u1_struct_0(sK6))) | ~sP0(X5,X6,sK7)) ) | ~spl13_10),
% 1.73/0.57    inference(superposition,[],[f66,f209])).
% 1.73/0.57  fof(f412,plain,(
% 1.73/0.57    ( ! [X0,X1] : (~v3_pre_topc(sK11(X1,X0,sK7),sK6) | sP0(X1,X0,sK6) | ~sP0(X1,X0,sK7)) ) | ~spl13_10),
% 1.73/0.57    inference(subsumption_resolution,[],[f411,f223])).
% 1.73/0.57  fof(f411,plain,(
% 1.73/0.57    ( ! [X0,X1] : (sP0(X1,X0,sK6) | ~v3_pre_topc(sK11(X1,X0,sK7),sK6) | ~m1_subset_1(sK11(X1,X0,sK7),k1_zfmisc_1(u1_struct_0(sK6))) | ~sP0(X1,X0,sK7)) ) | ~spl13_10),
% 1.73/0.57    inference(superposition,[],[f84,f224])).
% 1.73/0.57  fof(f224,plain,(
% 1.73/0.57    ( ! [X8,X7] : (k9_subset_1(u1_struct_0(sK6),X7,sK11(X8,X7,sK7)) = X8 | ~sP0(X8,X7,sK7)) ) | ~spl13_10),
% 1.73/0.57    inference(superposition,[],[f68,f209])).
% 1.73/0.57  fof(f68,plain,(
% 1.73/0.57    ( ! [X2,X0,X1] : (k9_subset_1(u1_struct_0(X2),X1,sK11(X0,X1,X2)) = X0 | ~sP0(X0,X1,X2)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f40])).
% 1.73/0.57  fof(f84,plain,(
% 1.73/0.57    ( ! [X2,X3,X1] : (sP0(k9_subset_1(u1_struct_0(X2),X1,X3),X1,X2) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.73/0.57    inference(equality_resolution,[],[f69])).
% 1.73/0.57  fof(f69,plain,(
% 1.73/0.57    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.73/0.57    inference(cnf_transformation,[],[f40])).
% 1.73/0.57  fof(f439,plain,(
% 1.73/0.57    ( ! [X4,X3] : (sP0(sK10(sK6,X3),X4,sK7) | ~r1_tarski(sK10(sK6,X3),X4) | ~sP1(sK7,X4) | sP1(sK6,X3)) ) | ~spl13_10),
% 1.73/0.57    inference(resolution,[],[f221,f63])).
% 1.73/0.57  fof(f63,plain,(
% 1.73/0.57    ( ! [X0,X1] : (m1_subset_1(sK10(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f36])).
% 1.73/0.57  fof(f221,plain,(
% 1.73/0.57    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) | ~r1_tarski(X2,X3) | sP0(X2,X3,sK7) | ~sP1(sK7,X3)) ) | ~spl13_10),
% 1.73/0.57    inference(superposition,[],[f62,f209])).
% 1.73/0.57  fof(f62,plain,(
% 1.73/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X3,X1) | sP0(X3,X1,X0) | ~sP1(X0,X1)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f36])).
% 1.73/0.57  fof(f299,plain,(
% 1.73/0.57    ( ! [X14,X13] : (~r1_tarski(X13,sK12(X14,sK7)) | ~v2_tex_2(sK12(X14,sK7),sK6) | sK12(X14,sK7) = X13 | ~sP3(X13,sK6) | sP3(X14,sK7)) ) | ~spl13_10),
% 1.73/0.57    inference(resolution,[],[f76,f226])).
% 1.73/0.57  fof(f76,plain,(
% 1.73/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | X0 = X3 | ~sP3(X0,X1)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f48])).
% 1.73/0.57  fof(f571,plain,(
% 1.73/0.57    ~spl13_3 | ~spl13_12),
% 1.73/0.57    inference(avatar_split_clause,[],[f138,f568,f109])).
% 1.73/0.57  fof(f109,plain,(
% 1.73/0.57    spl13_3 <=> v2_tex_2(sK8,sK7)),
% 1.73/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 1.73/0.57  fof(f138,plain,(
% 1.73/0.57    ~sP3(sK8,sK7) | ~v2_tex_2(sK8,sK7)),
% 1.73/0.57    inference(resolution,[],[f130,f75])).
% 1.73/0.57  fof(f75,plain,(
% 1.73/0.57    ( ! [X0,X1] : (sP4(X0,X1) | ~sP3(X1,X0) | ~v2_tex_2(X1,X0)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f44])).
% 1.73/0.57  fof(f130,plain,(
% 1.73/0.57    ~sP4(sK7,sK8)),
% 1.73/0.57    inference(subsumption_resolution,[],[f128,f85])).
% 1.73/0.57  fof(f85,plain,(
% 1.73/0.57    ~v3_tex_2(sK8,sK7)),
% 1.73/0.57    inference(forward_demodulation,[],[f56,f54])).
% 1.73/0.57  fof(f54,plain,(
% 1.73/0.57    sK8 = sK9),
% 1.73/0.57    inference(cnf_transformation,[],[f29])).
% 1.73/0.57  fof(f56,plain,(
% 1.73/0.57    ~v3_tex_2(sK9,sK7)),
% 1.73/0.57    inference(cnf_transformation,[],[f29])).
% 1.73/0.57  fof(f128,plain,(
% 1.73/0.57    ~sP4(sK7,sK8) | v3_tex_2(sK8,sK7)),
% 1.73/0.57    inference(resolution,[],[f124,f72])).
% 1.73/0.57  fof(f72,plain,(
% 1.73/0.57    ( ! [X0,X1] : (~sP5(X0,X1) | ~sP4(X1,X0) | v3_tex_2(X0,X1)) )),
% 1.73/0.57    inference(cnf_transformation,[],[f42])).
% 1.73/0.57  fof(f124,plain,(
% 1.73/0.57    sP5(sK8,sK7)),
% 1.73/0.57    inference(subsumption_resolution,[],[f120,f50])).
% 1.73/0.57  fof(f120,plain,(
% 1.73/0.57    sP5(sK8,sK7) | ~l1_pre_topc(sK7)),
% 1.73/0.57    inference(resolution,[],[f81,f86])).
% 1.73/0.57  fof(f86,plain,(
% 1.73/0.57    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK7)))),
% 1.73/0.57    inference(forward_demodulation,[],[f52,f54])).
% 1.73/0.57  fof(f52,plain,(
% 1.73/0.57    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK7)))),
% 1.73/0.57    inference(cnf_transformation,[],[f29])).
% 1.73/0.57  fof(f561,plain,(
% 1.73/0.57    ~spl13_2 | spl13_4 | ~spl13_9 | ~spl13_10),
% 1.73/0.57    inference(avatar_contradiction_clause,[],[f560])).
% 1.73/0.57  fof(f560,plain,(
% 1.73/0.57    $false | (~spl13_2 | spl13_4 | ~spl13_9 | ~spl13_10)),
% 1.73/0.57    inference(subsumption_resolution,[],[f550,f102])).
% 1.73/0.57  fof(f102,plain,(
% 1.73/0.57    sP1(sK6,sK8) | ~spl13_2),
% 1.73/0.57    inference(avatar_component_clause,[],[f101])).
% 1.73/0.57  fof(f101,plain,(
% 1.73/0.57    spl13_2 <=> sP1(sK6,sK8)),
% 1.73/0.57    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 1.73/0.57  fof(f550,plain,(
% 1.73/0.57    ~sP1(sK6,sK8) | (spl13_4 | ~spl13_9 | ~spl13_10)),
% 1.73/0.58    inference(resolution,[],[f549,f115])).
% 1.73/0.58  fof(f115,plain,(
% 1.73/0.58    ~sP1(sK7,sK8) | spl13_4),
% 1.73/0.58    inference(avatar_component_clause,[],[f113])).
% 1.73/0.58  fof(f113,plain,(
% 1.73/0.58    spl13_4 <=> sP1(sK7,sK8)),
% 1.73/0.58    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 1.73/0.58  fof(f549,plain,(
% 1.73/0.58    ( ! [X0] : (sP1(sK7,X0) | ~sP1(sK6,X0)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.58    inference(subsumption_resolution,[],[f548,f64])).
% 1.73/0.58  fof(f548,plain,(
% 1.73/0.58    ( ! [X0] : (sP1(sK7,X0) | ~r1_tarski(sK10(sK7,X0),X0) | ~sP1(sK6,X0)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.58    inference(duplicate_literal_removal,[],[f546])).
% 1.73/0.58  fof(f546,plain,(
% 1.73/0.58    ( ! [X0] : (sP1(sK7,X0) | ~r1_tarski(sK10(sK7,X0),X0) | sP1(sK7,X0) | ~sP1(sK6,X0)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.58    inference(resolution,[],[f544,f257])).
% 1.73/0.58  fof(f257,plain,(
% 1.73/0.58    ( ! [X2,X3] : (sP0(sK10(sK7,X2),X3,sK6) | ~r1_tarski(sK10(sK7,X2),X3) | sP1(sK7,X2) | ~sP1(sK6,X3)) ) | ~spl13_10),
% 1.73/0.58    inference(resolution,[],[f222,f62])).
% 1.73/0.58  fof(f222,plain,(
% 1.73/0.58    ( ! [X4] : (m1_subset_1(sK10(sK7,X4),k1_zfmisc_1(u1_struct_0(sK6))) | sP1(sK7,X4)) ) | ~spl13_10),
% 1.73/0.58    inference(superposition,[],[f63,f209])).
% 1.73/0.58  fof(f544,plain,(
% 1.73/0.58    ( ! [X0] : (~sP0(sK10(sK7,X0),X0,sK6) | sP1(sK7,X0)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.58    inference(resolution,[],[f537,f65])).
% 1.73/0.58  fof(f537,plain,(
% 1.73/0.58    ( ! [X0,X1] : (sP0(X1,X0,sK7) | ~sP0(X1,X0,sK6)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.58    inference(subsumption_resolution,[],[f467,f535])).
% 1.73/0.58  fof(f535,plain,(
% 1.73/0.58    ( ! [X2,X3] : (v3_pre_topc(sK11(X2,X3,sK6),sK7) | ~sP0(X2,X3,sK6)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.58    inference(subsumption_resolution,[],[f533,f49])).
% 1.73/0.58  fof(f533,plain,(
% 1.73/0.58    ( ! [X2,X3] : (v3_pre_topc(sK11(X2,X3,sK6),sK7) | ~sP0(X2,X3,sK6) | ~l1_pre_topc(sK6)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.58    inference(duplicate_literal_removal,[],[f532])).
% 1.73/0.58  fof(f532,plain,(
% 1.73/0.58    ( ! [X2,X3] : (v3_pre_topc(sK11(X2,X3,sK6),sK7) | ~sP0(X2,X3,sK6) | ~l1_pre_topc(sK6) | ~sP0(X2,X3,sK6)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.58    inference(resolution,[],[f356,f166])).
% 1.73/0.58  fof(f356,plain,(
% 1.73/0.58    ( ! [X4,X5] : (~r2_hidden(sK11(X4,X5,sK6),u1_pre_topc(sK6)) | v3_pre_topc(sK11(X4,X5,sK6),sK7) | ~sP0(X4,X5,sK6)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.58    inference(resolution,[],[f342,f66])).
% 1.73/0.58  fof(f342,plain,(
% 1.73/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | ~r2_hidden(X1,u1_pre_topc(sK6)) | v3_pre_topc(X1,sK7)) ) | (~spl13_9 | ~spl13_10)),
% 1.73/0.58    inference(forward_demodulation,[],[f230,f323])).
% 1.73/0.58  fof(f230,plain,(
% 1.73/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | ~r2_hidden(X1,u1_pre_topc(sK7)) | v3_pre_topc(X1,sK7)) ) | ~spl13_10),
% 1.73/0.58    inference(subsumption_resolution,[],[f220,f50])).
% 1.73/0.58  fof(f220,plain,(
% 1.73/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | ~r2_hidden(X1,u1_pre_topc(sK7)) | v3_pre_topc(X1,sK7) | ~l1_pre_topc(sK7)) ) | ~spl13_10),
% 1.73/0.58    inference(superposition,[],[f59,f209])).
% 1.73/0.58  fof(f467,plain,(
% 1.73/0.58    ( ! [X0,X1] : (~v3_pre_topc(sK11(X1,X0,sK6),sK7) | sP0(X1,X0,sK7) | ~sP0(X1,X0,sK6)) ) | ~spl13_10),
% 1.73/0.58    inference(subsumption_resolution,[],[f465,f66])).
% 1.73/0.58  fof(f465,plain,(
% 1.73/0.58    ( ! [X0,X1] : (sP0(X1,X0,sK7) | ~v3_pre_topc(sK11(X1,X0,sK6),sK7) | ~m1_subset_1(sK11(X1,X0,sK6),k1_zfmisc_1(u1_struct_0(sK6))) | ~sP0(X1,X0,sK6)) ) | ~spl13_10),
% 1.73/0.58    inference(superposition,[],[f270,f68])).
% 1.73/0.58  fof(f270,plain,(
% 1.73/0.58    ( ! [X0,X1] : (sP0(k9_subset_1(u1_struct_0(sK6),X0,X1),X0,sK7) | ~v3_pre_topc(X1,sK7) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) ) | ~spl13_10),
% 1.73/0.58    inference(superposition,[],[f84,f209])).
% 1.73/0.58  fof(f207,plain,(
% 1.73/0.58    spl13_9),
% 1.73/0.58    inference(avatar_contradiction_clause,[],[f206])).
% 1.73/0.58  fof(f206,plain,(
% 1.73/0.58    $false | spl13_9),
% 1.73/0.58    inference(subsumption_resolution,[],[f205,f50])).
% 1.73/0.58  fof(f205,plain,(
% 1.73/0.58    ~l1_pre_topc(sK7) | spl13_9),
% 1.73/0.58    inference(resolution,[],[f200,f57])).
% 1.73/0.58  fof(f57,plain,(
% 1.73/0.58    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f10])).
% 1.73/0.58  fof(f10,plain,(
% 1.73/0.58    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.73/0.58    inference(ennf_transformation,[],[f2])).
% 1.73/0.58  fof(f2,axiom,(
% 1.73/0.58    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.73/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.73/0.58  fof(f200,plain,(
% 1.73/0.58    ~m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) | spl13_9),
% 1.73/0.58    inference(avatar_component_clause,[],[f198])).
% 1.73/0.58  fof(f204,plain,(
% 1.73/0.58    ~spl13_9 | spl13_10),
% 1.73/0.58    inference(avatar_split_clause,[],[f194,f202,f198])).
% 1.73/0.58  fof(f194,plain,(
% 1.73/0.58    ( ! [X0,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) | u1_struct_0(sK7) = X0 | ~m1_subset_1(u1_pre_topc(sK7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))) )),
% 1.73/0.58    inference(superposition,[],[f82,f53])).
% 1.73/0.58  fof(f82,plain,(
% 1.73/0.58    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | X0 = X2 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.73/0.58    inference(cnf_transformation,[],[f16])).
% 1.73/0.58  fof(f137,plain,(
% 1.73/0.58    spl13_1),
% 1.73/0.58    inference(avatar_split_clause,[],[f134,f97])).
% 1.73/0.58  fof(f97,plain,(
% 1.73/0.58    spl13_1 <=> v2_tex_2(sK8,sK6)),
% 1.73/0.58    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 1.73/0.58  fof(f134,plain,(
% 1.73/0.58    v2_tex_2(sK8,sK6)),
% 1.73/0.58    inference(resolution,[],[f127,f73])).
% 1.73/0.58  fof(f73,plain,(
% 1.73/0.58    ( ! [X0,X1] : (~sP4(X0,X1) | v2_tex_2(X1,X0)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f44])).
% 1.73/0.58  fof(f116,plain,(
% 1.73/0.58    spl13_3 | ~spl13_4),
% 1.73/0.58    inference(avatar_split_clause,[],[f106,f113,f109])).
% 1.73/0.58  fof(f106,plain,(
% 1.73/0.58    ~sP1(sK7,sK8) | v2_tex_2(sK8,sK7)),
% 1.73/0.58    inference(resolution,[],[f93,f61])).
% 1.73/0.58  fof(f93,plain,(
% 1.73/0.58    sP2(sK8,sK7)),
% 1.73/0.58    inference(subsumption_resolution,[],[f90,f50])).
% 1.73/0.58  fof(f90,plain,(
% 1.73/0.58    sP2(sK8,sK7) | ~l1_pre_topc(sK7)),
% 1.73/0.58    inference(resolution,[],[f70,f86])).
% 1.73/0.58  fof(f105,plain,(
% 1.73/0.58    spl13_2 | ~spl13_1),
% 1.73/0.58    inference(avatar_split_clause,[],[f95,f97,f101])).
% 1.73/0.58  fof(f95,plain,(
% 1.73/0.58    ~v2_tex_2(sK8,sK6) | sP1(sK6,sK8)),
% 1.73/0.58    inference(resolution,[],[f92,f60])).
% 1.73/0.58  fof(f92,plain,(
% 1.73/0.58    sP2(sK8,sK6)),
% 1.73/0.58    inference(subsumption_resolution,[],[f89,f49])).
% 1.73/0.58  fof(f89,plain,(
% 1.73/0.58    sP2(sK8,sK6) | ~l1_pre_topc(sK6)),
% 1.73/0.58    inference(resolution,[],[f70,f51])).
% 1.73/0.58  % SZS output end Proof for theBenchmark
% 1.73/0.58  % (1163)------------------------------
% 1.73/0.58  % (1163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.58  % (1163)Termination reason: Refutation
% 1.73/0.58  
% 1.73/0.58  % (1163)Memory used [KB]: 6652
% 1.73/0.58  % (1163)Time elapsed: 0.154 s
% 1.73/0.58  % (1163)------------------------------
% 1.73/0.58  % (1163)------------------------------
% 1.73/0.58  % (1157)Success in time 0.22 s
%------------------------------------------------------------------------------
