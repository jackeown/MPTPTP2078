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
% DateTime   : Thu Dec  3 13:17:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 293 expanded)
%              Number of leaves         :   17 ( 105 expanded)
%              Depth                    :   22
%              Number of atoms          :  469 (2092 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f61,f74,f79,f82,f109,f123,f127])).

fof(f127,plain,
    ( spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f125,f55])).

fof(f55,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_3
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f125,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f124,f72])).

fof(f72,plain,
    ( l1_pre_topc(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_6
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f124,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f84,f68])).

fof(f68,plain,
    ( l1_pre_topc(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_5
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f84,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f60,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X1,X0)
      | r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f62,f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f42,f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f60,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_4
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f123,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f119,f68])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl4_1
    | spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f117,f33])).

fof(f33,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0) )
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0) )
            & m1_pre_topc(X2,sK0) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0) )
          & m1_pre_topc(X2,sK0) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0) )
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0) )
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0) )
   => ( ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_1
    | spl4_2
    | ~ spl4_6 ),
    inference(resolution,[],[f116,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f116,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl4_1
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f115,f72])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f112,f51])).

fof(f51,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_2
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f112,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f46,f63])).

fof(f46,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl4_1
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f109,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f107,f30])).

fof(f30,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f106,f47])).

fof(f47,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f106,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f102,f33])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f101,f68])).

fof(f101,plain,
    ( ! [X0] :
        ( r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK2) )
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f100,f31])).

fof(f31,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK2) )
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f98,f72])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK2) )
    | ~ spl4_3 ),
    inference(resolution,[],[f97,f56])).

fof(f56,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(X1,sK0)
      | r1_tsep_1(X0,X2)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(X1) ) ),
    inference(subsumption_resolution,[],[f96,f39])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,sK0)
      | r1_tsep_1(X0,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f95,f38])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,sK0)
      | r1_tsep_1(X0,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f93,f38])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,sK0)
      | r1_tsep_1(X0,X2)
      | ~ r1_tsep_1(X1,X2)
      | ~ l1_struct_0(X2)
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f92,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f92,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_xboole_0(u1_struct_0(X3),u1_struct_0(X5))
      | ~ m1_pre_topc(X4,sK0)
      | ~ m1_pre_topc(X4,X3)
      | ~ l1_pre_topc(X5)
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(X3,sK0)
      | r1_tsep_1(X4,X5) ) ),
    inference(resolution,[],[f90,f88])).

fof(f88,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(u1_struct_0(X2),X4)
      | ~ l1_pre_topc(X3)
      | ~ l1_pre_topc(X2)
      | ~ r1_xboole_0(X4,u1_struct_0(X3))
      | r1_tsep_1(X2,X3) ) ),
    inference(resolution,[],[f86,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f85,f38])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f37,f38])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f89,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f41,f28])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f82,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f80,f29])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_6 ),
    inference(resolution,[],[f76,f32])).

fof(f32,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_6 ),
    inference(resolution,[],[f73,f39])).

fof(f73,plain,
    ( ~ l1_pre_topc(sK3)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f79,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f78])).

fof(f78,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f77,f29])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_5 ),
    inference(resolution,[],[f75,f31])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_5 ),
    inference(resolution,[],[f69,f39])).

fof(f69,plain,
    ( ~ l1_pre_topc(sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f74,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f65,f58,f54,f71,f67])).

fof(f65,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl4_3
    | spl4_4 ),
    inference(subsumption_resolution,[],[f64,f59])).

fof(f59,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f64,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f63,f56])).

fof(f61,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f35,f58,f54])).

fof(f35,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f34,f49,f45])).

fof(f34,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:19:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (3480)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.48  % (3480)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f52,f61,f74,f79,f82,f109,f123,f127])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f126])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    $false | (spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f125,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ~r1_tsep_1(sK2,sK3) | spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    spl4_3 <=> r1_tsep_1(sK2,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    r1_tsep_1(sK2,sK3) | (~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f124,f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    l1_pre_topc(sK3) | ~spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl4_6 <=> l1_pre_topc(sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK3) | (~spl4_4 | ~spl4_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f84,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    l1_pre_topc(sK2) | ~spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl4_5 <=> l1_pre_topc(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    r1_tsep_1(sK2,sK3) | ~l1_pre_topc(sK2) | ~l1_pre_topc(sK3) | ~spl4_4),
% 0.22/0.48    inference(resolution,[],[f60,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tsep_1(X1,X0) | r1_tsep_1(X0,X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 0.22/0.48    inference(resolution,[],[f62,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_struct_0(X0) | r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.22/0.48    inference(resolution,[],[f42,f38])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    r1_tsep_1(sK3,sK2) | ~spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl4_4 <=> r1_tsep_1(sK3,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ~spl4_1 | spl4_2 | ~spl4_5 | ~spl4_6),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f122])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    $false | (~spl4_1 | spl4_2 | ~spl4_5 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f119,f68])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ~l1_pre_topc(sK2) | (~spl4_1 | spl4_2 | ~spl4_6)),
% 0.22/0.48    inference(resolution,[],[f117,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    m1_pre_topc(sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ((((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0)) & m1_pre_topc(sK2,sK0)) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f24,f23,f22,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(X1,sK0)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) & m1_pre_topc(sK1,sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(X2,sK0)) => (? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) & m1_pre_topc(sK2,sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ? [X3] : ((r1_tsep_1(X3,sK2) | r1_tsep_1(sK2,X3)) & (~r1_tsep_1(X3,sK1) | ~r1_tsep_1(sK1,X3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0)) => ((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)) & (~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.48    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.22/0.48  fof(f117,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | (~spl4_1 | spl4_2 | ~spl4_6)),
% 0.22/0.48    inference(resolution,[],[f116,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ~l1_pre_topc(sK1) | (~spl4_1 | spl4_2 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f115,f72])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ~l1_pre_topc(sK3) | ~l1_pre_topc(sK1) | (~spl4_1 | spl4_2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f112,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ~r1_tsep_1(sK3,sK1) | spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    spl4_2 <=> r1_tsep_1(sK3,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    r1_tsep_1(sK3,sK1) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK1) | ~spl4_1),
% 0.22/0.48    inference(resolution,[],[f46,f63])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    r1_tsep_1(sK1,sK3) | ~spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    spl4_1 <=> r1_tsep_1(sK1,sK3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_6),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    $false | (spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f107,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    m1_pre_topc(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ~m1_pre_topc(sK1,sK0) | (spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f106,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ~r1_tsep_1(sK1,sK3) | spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f45])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    r1_tsep_1(sK1,sK3) | ~m1_pre_topc(sK1,sK0) | (~spl4_3 | ~spl4_5 | ~spl4_6)),
% 0.22/0.48    inference(resolution,[],[f102,f33])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK0)) ) | (~spl4_3 | ~spl4_5 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f101,f68])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK2)) ) | (~spl4_3 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f100,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    m1_pre_topc(sK2,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(sK2,sK0) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK2)) ) | (~spl4_3 | ~spl4_6)),
% 0.22/0.48    inference(subsumption_resolution,[],[f98,f72])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(sK3) | ~m1_pre_topc(sK2,sK0) | r1_tsep_1(X0,sK3) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK2)) ) | ~spl4_3),
% 0.22/0.48    inference(resolution,[],[f97,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    r1_tsep_1(sK2,sK3) | ~spl4_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f54])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_tsep_1(X1,X2) | ~l1_pre_topc(X2) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X0,X2) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f96,f39])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X2) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X0,X2) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(X1)) )),
% 0.22/0.48    inference(resolution,[],[f95,f38])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~l1_struct_0(X1) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X2) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X0,X2) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X0,sK0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f93,f38])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X2) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,sK0) | r1_tsep_1(X0,X2) | ~r1_tsep_1(X1,X2) | ~l1_struct_0(X2) | ~l1_struct_0(X1)) )),
% 0.22/0.48    inference(resolution,[],[f92,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~r1_xboole_0(u1_struct_0(X3),u1_struct_0(X5)) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X4,X3) | ~l1_pre_topc(X5) | ~l1_pre_topc(X4) | ~m1_pre_topc(X3,sK0) | r1_tsep_1(X4,X5)) )),
% 0.22/0.48    inference(resolution,[],[f90,f88])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ( ! [X4,X2,X3] : (~r1_tarski(u1_struct_0(X2),X4) | ~l1_pre_topc(X3) | ~l1_pre_topc(X2) | ~r1_xboole_0(X4,u1_struct_0(X3)) | r1_tsep_1(X2,X3)) )),
% 0.22/0.48    inference(resolution,[],[f86,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.48    inference(resolution,[],[f85,f38])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_struct_0(X0) | r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1)) )),
% 0.22/0.48    inference(resolution,[],[f37,f38])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f89,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) )),
% 0.22/0.48    inference(resolution,[],[f41,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    v2_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    spl4_6),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f81])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    $false | spl4_6),
% 0.22/0.48    inference(subsumption_resolution,[],[f80,f29])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | spl4_6),
% 0.22/0.48    inference(resolution,[],[f76,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    m1_pre_topc(sK3,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl4_6),
% 0.22/0.48    inference(resolution,[],[f73,f39])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ~l1_pre_topc(sK3) | spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl4_5),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    $false | spl4_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f77,f29])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | spl4_5),
% 0.22/0.48    inference(resolution,[],[f75,f31])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl4_5),
% 0.22/0.48    inference(resolution,[],[f69,f39])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ~l1_pre_topc(sK2) | spl4_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ~spl4_5 | ~spl4_6 | ~spl4_3 | spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f65,f58,f54,f71,f67])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ~l1_pre_topc(sK3) | ~l1_pre_topc(sK2) | (~spl4_3 | spl4_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f64,f59])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ~r1_tsep_1(sK3,sK2) | spl4_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    r1_tsep_1(sK3,sK2) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~spl4_3),
% 0.22/0.48    inference(resolution,[],[f63,f56])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    spl4_3 | spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f58,f54])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ~spl4_1 | ~spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f49,f45])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (3480)------------------------------
% 0.22/0.48  % (3480)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (3480)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (3480)Memory used [KB]: 5373
% 0.22/0.48  % (3480)Time elapsed: 0.056 s
% 0.22/0.48  % (3480)------------------------------
% 0.22/0.48  % (3480)------------------------------
% 0.22/0.48  % (3494)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.48  % (3479)Success in time 0.12 s
%------------------------------------------------------------------------------
