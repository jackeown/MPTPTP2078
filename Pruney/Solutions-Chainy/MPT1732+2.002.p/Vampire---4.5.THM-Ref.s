%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:09 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 760 expanded)
%              Number of leaves         :   26 ( 326 expanded)
%              Depth                    :   15
%              Number of atoms          :  952 (10426 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f376,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f80,f93,f100,f105,f114,f189,f220,f228,f238,f255,f263,f271,f353,f375])).

fof(f375,plain,
    ( spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f373,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ( ( r1_tsep_1(sK3,sK2)
          | r1_tsep_1(sK3,sK1) )
        & ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) )
      | ( ( r1_tsep_1(sK2,sK3)
          | r1_tsep_1(sK1,sK3) )
        & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ) )
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) )
                        & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                      | ( ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) )
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X3,X1) )
                    & ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2)) )
                  | ( ( r1_tsep_1(X2,X3)
                      | r1_tsep_1(X1,X3) )
                    & ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3) ) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X3,sK1) )
                  & ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2)) )
                | ( ( r1_tsep_1(X2,X3)
                    | r1_tsep_1(sK1,X3) )
                  & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3) ) )
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X3,sK1) )
                & ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2)) )
              | ( ( r1_tsep_1(X2,X3)
                  | r1_tsep_1(sK1,X3) )
                & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3) ) )
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ( r1_tsep_1(X3,sK2)
                | r1_tsep_1(X3,sK1) )
              & ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2)) )
            | ( ( r1_tsep_1(sK2,X3)
                | r1_tsep_1(sK1,X3) )
              & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3) ) )
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( ( ( r1_tsep_1(X3,sK2)
              | r1_tsep_1(X3,sK1) )
            & ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2)) )
          | ( ( r1_tsep_1(sK2,X3)
              | r1_tsep_1(sK1,X3) )
            & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3) ) )
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ( ( r1_tsep_1(sK3,sK2)
            | r1_tsep_1(sK3,sK1) )
          & ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) )
        | ( ( r1_tsep_1(sK2,sK3)
            | r1_tsep_1(sK1,sK3) )
          & ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                         => ( ~ r1_tsep_1(X3,X2)
                            & ~ r1_tsep_1(X3,X1) ) )
                        & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                         => ( ~ r1_tsep_1(X2,X3)
                            & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                       => ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X3,X1) ) )
                      & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                       => ( ~ r1_tsep_1(X2,X3)
                          & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).

fof(f373,plain,
    ( v2_struct_0(sK0)
    | spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f372,f30])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f372,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f371,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f371,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f370,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f370,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f369,f33])).

fof(f33,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f369,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f368,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f368,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f367,f35])).

fof(f35,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f367,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f366,f38])).

fof(f38,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f366,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_20 ),
    inference(resolution,[],[f360,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
             => ( ~ r1_tsep_1(X1,X2)
               => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).

fof(f360,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | spl4_2
    | ~ spl4_13
    | spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f359,f210])).

fof(f210,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl4_13
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f359,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_2
    | spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f354,f214])).

fof(f214,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl4_14
  <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f354,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_2
    | ~ spl4_20 ),
    inference(resolution,[],[f352,f62])).

fof(f62,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_2
  <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f352,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,sK2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl4_20
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK2)
        | r1_tsep_1(sK3,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f353,plain,
    ( spl4_11
    | spl4_20
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f295,f77,f351,f184])).

fof(f184,plain,
    ( spl4_11
  <=> ! [X3] :
        ( ~ m1_pre_topc(X3,sK3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f77,plain,
    ( spl4_6
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r1_tsep_1(sK3,X0) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f294,f36])).

fof(f36,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f294,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r1_tsep_1(sK3,X0) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f293,f37])).

fof(f37,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r1_tsep_1(sK3,X0) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f292,f34])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X1,sK3)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r1_tsep_1(sK3,X0) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f290,f35])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X1,sK3)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | r1_tsep_1(sK3,X0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f79,f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | r1_tsep_1(X0,X2) ) ),
    inference(subsumption_resolution,[],[f134,f29])).

fof(f134,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | r1_tsep_1(X0,X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f133,f31])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(sK0)
      | r1_tsep_1(X0,X2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f48,f30])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tsep_1(X2,X4)
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X2,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r1_tsep_1(X4,X1)
                        & r1_tsep_1(X2,X3) )
                      | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        & ~ r1_tsep_1(X2,X4) )
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r1_tsep_1(X4,X1)
                        & r1_tsep_1(X2,X3) )
                      | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        & ~ r1_tsep_1(X2,X4) )
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => ( ( r1_tsep_1(X4,X1)
                            & r1_tsep_1(X2,X3) )
                          | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                            & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tmap_1)).

fof(f79,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f77])).

% (19934)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
fof(f271,plain,
    ( ~ spl4_8
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f269,f91])).

fof(f91,plain,
    ( l1_pre_topc(sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_8
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f269,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f268,f37])).

fof(f268,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK3)
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f264,f36])).

fof(f264,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK3)
    | ~ spl4_11 ),
    inference(resolution,[],[f185,f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f185,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0) )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f184])).

fof(f263,plain,(
    ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f261,f29])).

fof(f261,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f260,f31])).

fof(f260,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f259,f32])).

fof(f259,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f258,f33])).

fof(f258,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f257,f34])).

fof(f257,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f256,f35])).

fof(f256,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_14 ),
    inference(resolution,[],[f215,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f215,plain,
    ( v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f213])).

fof(f255,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f250,f218])).

fof(f218,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl4_15
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f250,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(resolution,[],[f247,f87])).

fof(f87,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_7
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f246,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f246,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f245,f91])).

fof(f245,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK3)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f240,f58])).

fof(f58,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_1
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f240,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | ~ l1_pre_topc(k2_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f61,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X1,X0)
      | r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f81,f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f52,f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f61,plain,
    ( r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f238,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f236,f29])).

fof(f236,plain,
    ( v2_struct_0(sK0)
    | spl4_15 ),
    inference(subsumption_resolution,[],[f235,f30])).

fof(f235,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_15 ),
    inference(subsumption_resolution,[],[f234,f31])).

fof(f234,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_15 ),
    inference(subsumption_resolution,[],[f233,f32])).

fof(f233,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_15 ),
    inference(subsumption_resolution,[],[f232,f33])).

fof(f232,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_15 ),
    inference(subsumption_resolution,[],[f231,f34])).

fof(f231,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_15 ),
    inference(subsumption_resolution,[],[f230,f35])).

fof(f230,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_15 ),
    inference(subsumption_resolution,[],[f229,f38])).

fof(f229,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_15 ),
    inference(resolution,[],[f219,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f219,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f217])).

fof(f228,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f226,f29])).

fof(f226,plain,
    ( v2_struct_0(sK0)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f225,f31])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f224,f32])).

fof(f224,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f223,f33])).

fof(f223,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f222,f34])).

fof(f222,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_13 ),
    inference(subsumption_resolution,[],[f221,f35])).

fof(f221,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_13 ),
    inference(resolution,[],[f211,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f211,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f209])).

fof(f220,plain,
    ( ~ spl4_13
    | spl4_14
    | ~ spl4_15
    | spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f190,f187,f60,f217,f213,f209])).

fof(f187,plain,
    ( spl4_12
  <=> ! [X2] :
        ( ~ m1_pre_topc(X2,sK1)
        | r1_tsep_1(sK3,X2)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f190,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_2
    | ~ spl4_12 ),
    inference(resolution,[],[f188,f62])).

fof(f188,plain,
    ( ! [X2] :
        ( r1_tsep_1(sK3,X2)
        | ~ m1_pre_topc(X2,sK1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f187])).

fof(f189,plain,
    ( spl4_11
    | spl4_12
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f145,f73,f187,f184])).

fof(f73,plain,
    ( spl4_5
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f145,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | r1_tsep_1(sK3,X2) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f144,f36])).

fof(f144,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | r1_tsep_1(sK3,X2) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f143,f37])).

fof(f143,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | r1_tsep_1(sK3,X2) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f142,f32])).

fof(f142,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(X3,sK3)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | r1_tsep_1(sK3,X2) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f137,f33])).

fof(f137,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(X3,sK3)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | r1_tsep_1(sK3,X2) )
    | ~ spl4_5 ),
    inference(resolution,[],[f135,f75])).

fof(f75,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f114,plain,
    ( ~ spl4_4
    | spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | ~ spl4_4
    | spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f110,f31])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_4
    | spl4_6
    | ~ spl4_8 ),
    inference(resolution,[],[f109,f35])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl4_4
    | spl4_6
    | ~ spl4_8 ),
    inference(resolution,[],[f108,f45])).

fof(f108,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ spl4_4
    | spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f107,f91])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f106,f78])).

fof(f78,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f106,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f71,f82])).

fof(f71,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_4
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f105,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f101,f31])).

fof(f101,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_8 ),
    inference(resolution,[],[f95,f37])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_8 ),
    inference(resolution,[],[f92,f45])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK3)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f100,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f96,f31])).

fof(f96,plain,
    ( ~ l1_pre_topc(sK0)
    | spl4_7 ),
    inference(resolution,[],[f94,f33])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl4_7 ),
    inference(resolution,[],[f88,f45])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f93,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | ~ spl4_3
    | spl4_5 ),
    inference(avatar_split_clause,[],[f84,f73,f65,f90,f86])).

fof(f65,plain,
    ( spl4_3
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_3
    | spl4_5 ),
    inference(subsumption_resolution,[],[f83,f74])).

fof(f74,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f83,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f82,f67])).

fof(f67,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f80,plain,
    ( spl4_3
    | spl4_4
    | spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f42,f77,f73,f69,f65])).

fof(f42,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f39,f60,f56])).

fof(f39,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:59:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (19929)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.48  % (19930)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.48  % (19921)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (19922)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.50  % (19925)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (19933)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.50  % (19923)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.51  % (19919)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.52  % (19917)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (19932)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.53  % (19920)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.53  % (19937)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% 0.22/0.53  % (19918)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.53  % (19931)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.54  % (19927)WARNING: option uwaf not known.
% 0.22/0.54  % (19936)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 1.40/0.54  % (19927)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 1.40/0.54  % (19917)Refutation found. Thanks to Tanya!
% 1.40/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % (19924)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f376,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(avatar_sat_refutation,[],[f63,f80,f93,f100,f105,f114,f189,f220,f228,f238,f255,f263,f271,f353,f375])).
% 1.40/0.54  fof(f375,plain,(
% 1.40/0.54    spl4_2 | ~spl4_13 | spl4_14 | ~spl4_20),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f374])).
% 1.40/0.54  fof(f374,plain,(
% 1.40/0.54    $false | (spl4_2 | ~spl4_13 | spl4_14 | ~spl4_20)),
% 1.40/0.54    inference(subsumption_resolution,[],[f373,f29])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    ~v2_struct_0(sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f28])).
% 1.40/0.54  fof(f28,plain,(
% 1.40/0.54    ((((((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1)) & ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))) | ((r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f27,f26,f25,f24])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f25,plain,(
% 1.40/0.54    ? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(sK1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f26,plain,(
% 1.40/0.54    ? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(sK1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((((r1_tsep_1(X3,sK2) | r1_tsep_1(X3,sK1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2))) | ((r1_tsep_1(sK2,X3) | r1_tsep_1(sK1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f27,plain,(
% 1.40/0.54    ? [X3] : ((((r1_tsep_1(X3,sK2) | r1_tsep_1(X3,sK1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2))) | ((r1_tsep_1(sK2,X3) | r1_tsep_1(sK1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => ((((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1)) & ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))) | ((r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f12,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f11])).
% 1.40/0.54  fof(f11,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f9])).
% 1.40/0.54  fof(f9,negated_conjecture,(
% 1.40/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) => (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X3,X1))) & (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) => (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X1,X3)))))))))),
% 1.40/0.54    inference(negated_conjecture,[],[f8])).
% 1.40/0.54  fof(f8,conjecture,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) => (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X3,X1))) & (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) => (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X1,X3)))))))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).
% 1.40/0.54  fof(f373,plain,(
% 1.40/0.54    v2_struct_0(sK0) | (spl4_2 | ~spl4_13 | spl4_14 | ~spl4_20)),
% 1.40/0.54    inference(subsumption_resolution,[],[f372,f30])).
% 1.40/0.54  fof(f30,plain,(
% 1.40/0.54    v2_pre_topc(sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f28])).
% 1.40/0.54  fof(f372,plain,(
% 1.40/0.54    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_2 | ~spl4_13 | spl4_14 | ~spl4_20)),
% 1.40/0.54    inference(subsumption_resolution,[],[f371,f31])).
% 1.40/0.54  fof(f31,plain,(
% 1.40/0.54    l1_pre_topc(sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f28])).
% 1.40/0.54  fof(f371,plain,(
% 1.40/0.54    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_2 | ~spl4_13 | spl4_14 | ~spl4_20)),
% 1.40/0.54    inference(subsumption_resolution,[],[f370,f32])).
% 1.40/0.54  fof(f32,plain,(
% 1.40/0.54    ~v2_struct_0(sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f28])).
% 1.40/0.54  fof(f370,plain,(
% 1.40/0.54    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_2 | ~spl4_13 | spl4_14 | ~spl4_20)),
% 1.40/0.54    inference(subsumption_resolution,[],[f369,f33])).
% 1.40/0.54  fof(f33,plain,(
% 1.40/0.54    m1_pre_topc(sK1,sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f28])).
% 1.40/0.54  fof(f369,plain,(
% 1.40/0.54    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_2 | ~spl4_13 | spl4_14 | ~spl4_20)),
% 1.40/0.54    inference(subsumption_resolution,[],[f368,f34])).
% 1.40/0.54  fof(f34,plain,(
% 1.40/0.54    ~v2_struct_0(sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f28])).
% 1.40/0.54  fof(f368,plain,(
% 1.40/0.54    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_2 | ~spl4_13 | spl4_14 | ~spl4_20)),
% 1.40/0.54    inference(subsumption_resolution,[],[f367,f35])).
% 1.40/0.54  fof(f35,plain,(
% 1.40/0.54    m1_pre_topc(sK2,sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f28])).
% 1.40/0.54  fof(f367,plain,(
% 1.40/0.54    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_2 | ~spl4_13 | spl4_14 | ~spl4_20)),
% 1.40/0.54    inference(subsumption_resolution,[],[f366,f38])).
% 1.40/0.54  fof(f38,plain,(
% 1.40/0.54    ~r1_tsep_1(sK1,sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f28])).
% 1.40/0.54  fof(f366,plain,(
% 1.40/0.54    r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl4_2 | ~spl4_13 | spl4_14 | ~spl4_20)),
% 1.40/0.54    inference(resolution,[],[f360,f47])).
% 1.40/0.54  fof(f47,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f17])).
% 1.40/0.54  fof(f17,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f16])).
% 1.40/0.54  fof(f16,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f6])).
% 1.40/0.54  fof(f6,axiom,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1))))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).
% 1.40/0.54  fof(f360,plain,(
% 1.40/0.54    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (spl4_2 | ~spl4_13 | spl4_14 | ~spl4_20)),
% 1.40/0.54    inference(subsumption_resolution,[],[f359,f210])).
% 1.40/0.54  fof(f210,plain,(
% 1.40/0.54    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | ~spl4_13),
% 1.40/0.54    inference(avatar_component_clause,[],[f209])).
% 1.40/0.54  fof(f209,plain,(
% 1.40/0.54    spl4_13 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.40/0.54  fof(f359,plain,(
% 1.40/0.54    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | (spl4_2 | spl4_14 | ~spl4_20)),
% 1.40/0.54    inference(subsumption_resolution,[],[f354,f214])).
% 1.40/0.54  fof(f214,plain,(
% 1.40/0.54    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | spl4_14),
% 1.40/0.54    inference(avatar_component_clause,[],[f213])).
% 1.40/0.54  fof(f213,plain,(
% 1.40/0.54    spl4_14 <=> v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.40/0.54  fof(f354,plain,(
% 1.40/0.54    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | (spl4_2 | ~spl4_20)),
% 1.40/0.54    inference(resolution,[],[f352,f62])).
% 1.40/0.54  fof(f62,plain,(
% 1.40/0.54    ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | spl4_2),
% 1.40/0.54    inference(avatar_component_clause,[],[f60])).
% 1.40/0.54  fof(f60,plain,(
% 1.40/0.54    spl4_2 <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.40/0.54  fof(f352,plain,(
% 1.40/0.54    ( ! [X0] : (r1_tsep_1(sK3,X0) | ~m1_pre_topc(X0,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0)) ) | ~spl4_20),
% 1.40/0.54    inference(avatar_component_clause,[],[f351])).
% 1.40/0.54  fof(f351,plain,(
% 1.40/0.54    spl4_20 <=> ! [X0] : (~m1_pre_topc(X0,sK2) | r1_tsep_1(sK3,X0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.40/0.54  fof(f353,plain,(
% 1.40/0.54    spl4_11 | spl4_20 | ~spl4_6),
% 1.40/0.54    inference(avatar_split_clause,[],[f295,f77,f351,f184])).
% 1.40/0.54  fof(f184,plain,(
% 1.40/0.54    spl4_11 <=> ! [X3] : (~m1_pre_topc(X3,sK3) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.40/0.54  fof(f77,plain,(
% 1.40/0.54    spl4_6 <=> r1_tsep_1(sK3,sK2)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.40/0.54  fof(f295,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tsep_1(sK3,X0)) ) | ~spl4_6),
% 1.40/0.54    inference(subsumption_resolution,[],[f294,f36])).
% 1.40/0.54  fof(f36,plain,(
% 1.40/0.54    ~v2_struct_0(sK3)),
% 1.40/0.54    inference(cnf_transformation,[],[f28])).
% 1.40/0.54  fof(f294,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tsep_1(sK3,X0)) ) | ~spl4_6),
% 1.40/0.54    inference(subsumption_resolution,[],[f293,f37])).
% 1.40/0.54  fof(f37,plain,(
% 1.40/0.54    m1_pre_topc(sK3,sK0)),
% 1.40/0.54    inference(cnf_transformation,[],[f28])).
% 1.40/0.54  fof(f293,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tsep_1(sK3,X0)) ) | ~spl4_6),
% 1.40/0.54    inference(subsumption_resolution,[],[f292,f34])).
% 1.40/0.54  fof(f292,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK3) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tsep_1(sK3,X0)) ) | ~spl4_6),
% 1.40/0.54    inference(subsumption_resolution,[],[f290,f35])).
% 1.40/0.54  fof(f290,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK3) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | r1_tsep_1(sK3,X0)) ) | ~spl4_6),
% 1.40/0.54    inference(resolution,[],[f79,f135])).
% 1.40/0.54  fof(f135,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | r1_tsep_1(X0,X2)) )),
% 1.40/0.54    inference(subsumption_resolution,[],[f134,f29])).
% 1.40/0.54  fof(f134,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | r1_tsep_1(X0,X2) | v2_struct_0(sK0)) )),
% 1.40/0.54    inference(subsumption_resolution,[],[f133,f31])).
% 1.40/0.54  fof(f133,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | ~l1_pre_topc(sK0) | r1_tsep_1(X0,X2) | v2_struct_0(sK0)) )),
% 1.40/0.54    inference(resolution,[],[f48,f30])).
% 1.40/0.54  fof(f48,plain,(
% 1.40/0.54    ( ! [X4,X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tsep_1(X2,X4) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_tsep_1(X2,X3) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r1_tsep_1(X4,X1) & r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) & ~r1_tsep_1(X2,X4)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f18])).
% 1.40/0.54  fof(f18,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((((r1_tsep_1(X4,X1) & r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) & ~r1_tsep_1(X2,X4))) | (~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f7])).
% 1.40/0.54  fof(f7,axiom,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => ((r1_tsep_1(X4,X1) & r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) & ~r1_tsep_1(X2,X4)))))))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tmap_1)).
% 1.40/0.54  fof(f79,plain,(
% 1.40/0.54    r1_tsep_1(sK3,sK2) | ~spl4_6),
% 1.40/0.54    inference(avatar_component_clause,[],[f77])).
% 1.40/0.54  % (19934)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 1.40/0.54  fof(f271,plain,(
% 1.40/0.54    ~spl4_8 | ~spl4_11),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f270])).
% 1.40/0.54  fof(f270,plain,(
% 1.40/0.54    $false | (~spl4_8 | ~spl4_11)),
% 1.40/0.54    inference(subsumption_resolution,[],[f269,f91])).
% 1.40/0.54  fof(f91,plain,(
% 1.40/0.54    l1_pre_topc(sK3) | ~spl4_8),
% 1.40/0.54    inference(avatar_component_clause,[],[f90])).
% 1.40/0.54  fof(f90,plain,(
% 1.40/0.54    spl4_8 <=> l1_pre_topc(sK3)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.40/0.54  fof(f269,plain,(
% 1.40/0.54    ~l1_pre_topc(sK3) | ~spl4_11),
% 1.40/0.54    inference(subsumption_resolution,[],[f268,f37])).
% 1.40/0.54  fof(f268,plain,(
% 1.40/0.54    ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK3) | ~spl4_11),
% 1.40/0.54    inference(subsumption_resolution,[],[f264,f36])).
% 1.40/0.54  fof(f264,plain,(
% 1.40/0.54    v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK3) | ~spl4_11),
% 1.40/0.54    inference(resolution,[],[f185,f44])).
% 1.40/0.54  fof(f44,plain,(
% 1.40/0.54    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f14])).
% 1.40/0.54  fof(f14,plain,(
% 1.40/0.54    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.40/0.54  fof(f185,plain,(
% 1.40/0.54    ( ! [X3] : (~m1_pre_topc(X3,sK3) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0)) ) | ~spl4_11),
% 1.40/0.54    inference(avatar_component_clause,[],[f184])).
% 1.40/0.54  fof(f263,plain,(
% 1.40/0.54    ~spl4_14),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f262])).
% 1.40/0.54  fof(f262,plain,(
% 1.40/0.54    $false | ~spl4_14),
% 1.40/0.54    inference(subsumption_resolution,[],[f261,f29])).
% 1.40/0.54  fof(f261,plain,(
% 1.40/0.54    v2_struct_0(sK0) | ~spl4_14),
% 1.40/0.54    inference(subsumption_resolution,[],[f260,f31])).
% 1.40/0.54  fof(f260,plain,(
% 1.40/0.54    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_14),
% 1.40/0.54    inference(subsumption_resolution,[],[f259,f32])).
% 1.40/0.54  fof(f259,plain,(
% 1.40/0.54    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_14),
% 1.40/0.54    inference(subsumption_resolution,[],[f258,f33])).
% 1.40/0.54  fof(f258,plain,(
% 1.40/0.54    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_14),
% 1.40/0.54    inference(subsumption_resolution,[],[f257,f34])).
% 1.40/0.54  fof(f257,plain,(
% 1.40/0.54    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_14),
% 1.40/0.54    inference(subsumption_resolution,[],[f256,f35])).
% 1.40/0.54  fof(f256,plain,(
% 1.40/0.54    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl4_14),
% 1.40/0.54    inference(resolution,[],[f215,f53])).
% 1.40/0.54  fof(f53,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f23])).
% 1.40/0.54  fof(f23,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f22])).
% 1.40/0.54  fof(f22,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f10])).
% 1.40/0.54  fof(f10,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.40/0.54    inference(pure_predicate_removal,[],[f3])).
% 1.40/0.54  fof(f3,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 1.40/0.54  fof(f215,plain,(
% 1.40/0.54    v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl4_14),
% 1.40/0.54    inference(avatar_component_clause,[],[f213])).
% 1.40/0.54  fof(f255,plain,(
% 1.40/0.54    spl4_1 | ~spl4_2 | ~spl4_7 | ~spl4_8 | ~spl4_15),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f254])).
% 1.40/0.54  fof(f254,plain,(
% 1.40/0.54    $false | (spl4_1 | ~spl4_2 | ~spl4_7 | ~spl4_8 | ~spl4_15)),
% 1.40/0.54    inference(subsumption_resolution,[],[f250,f218])).
% 1.40/0.54  fof(f218,plain,(
% 1.40/0.54    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | ~spl4_15),
% 1.40/0.54    inference(avatar_component_clause,[],[f217])).
% 1.40/0.54  fof(f217,plain,(
% 1.40/0.54    spl4_15 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.40/0.54  fof(f250,plain,(
% 1.40/0.54    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | (spl4_1 | ~spl4_2 | ~spl4_7 | ~spl4_8)),
% 1.40/0.54    inference(resolution,[],[f247,f87])).
% 1.40/0.54  fof(f87,plain,(
% 1.40/0.54    l1_pre_topc(sK1) | ~spl4_7),
% 1.40/0.54    inference(avatar_component_clause,[],[f86])).
% 1.40/0.54  fof(f86,plain,(
% 1.40/0.54    spl4_7 <=> l1_pre_topc(sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.40/0.54  fof(f247,plain,(
% 1.40/0.54    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)) ) | (spl4_1 | ~spl4_2 | ~spl4_8)),
% 1.40/0.54    inference(resolution,[],[f246,f45])).
% 1.40/0.54  fof(f45,plain,(
% 1.40/0.54    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f15])).
% 1.40/0.54  fof(f15,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f2])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.40/0.54  fof(f246,plain,(
% 1.40/0.54    ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | (spl4_1 | ~spl4_2 | ~spl4_8)),
% 1.40/0.54    inference(subsumption_resolution,[],[f245,f91])).
% 1.40/0.54  fof(f245,plain,(
% 1.40/0.54    ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(sK3) | (spl4_1 | ~spl4_2)),
% 1.40/0.54    inference(subsumption_resolution,[],[f240,f58])).
% 1.40/0.54  fof(f58,plain,(
% 1.40/0.54    ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | spl4_1),
% 1.40/0.54    inference(avatar_component_clause,[],[f56])).
% 1.40/0.54  fof(f56,plain,(
% 1.40/0.54    spl4_1 <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.40/0.54  fof(f240,plain,(
% 1.40/0.54    r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | ~l1_pre_topc(k2_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(sK3) | ~spl4_2),
% 1.40/0.54    inference(resolution,[],[f61,f82])).
% 1.40/0.54  fof(f82,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r1_tsep_1(X1,X0) | r1_tsep_1(X0,X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1)) )),
% 1.40/0.54    inference(resolution,[],[f81,f43])).
% 1.40/0.54  fof(f43,plain,(
% 1.40/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f13])).
% 1.40/0.54  fof(f13,plain,(
% 1.40/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.40/0.54  fof(f81,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~l1_struct_0(X0) | r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X1)) )),
% 1.40/0.54    inference(resolution,[],[f52,f43])).
% 1.40/0.54  fof(f52,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f21])).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.40/0.54    inference(flattening,[],[f20])).
% 1.40/0.54  fof(f20,plain,(
% 1.40/0.54    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f4])).
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 1.40/0.54  fof(f61,plain,(
% 1.40/0.54    r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | ~spl4_2),
% 1.40/0.54    inference(avatar_component_clause,[],[f60])).
% 1.40/0.54  fof(f238,plain,(
% 1.40/0.54    spl4_15),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f237])).
% 1.40/0.55  fof(f237,plain,(
% 1.40/0.55    $false | spl4_15),
% 1.40/0.55    inference(subsumption_resolution,[],[f236,f29])).
% 1.40/0.55  fof(f236,plain,(
% 1.40/0.55    v2_struct_0(sK0) | spl4_15),
% 1.40/0.55    inference(subsumption_resolution,[],[f235,f30])).
% 1.40/0.55  fof(f235,plain,(
% 1.40/0.55    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_15),
% 1.40/0.55    inference(subsumption_resolution,[],[f234,f31])).
% 1.40/0.55  fof(f234,plain,(
% 1.40/0.55    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_15),
% 1.40/0.55    inference(subsumption_resolution,[],[f233,f32])).
% 1.40/0.55  fof(f233,plain,(
% 1.40/0.55    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_15),
% 1.40/0.55    inference(subsumption_resolution,[],[f232,f33])).
% 1.40/0.55  fof(f232,plain,(
% 1.40/0.55    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_15),
% 1.40/0.55    inference(subsumption_resolution,[],[f231,f34])).
% 1.40/0.55  fof(f231,plain,(
% 1.40/0.55    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_15),
% 1.40/0.55    inference(subsumption_resolution,[],[f230,f35])).
% 1.40/0.55  fof(f230,plain,(
% 1.40/0.55    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_15),
% 1.40/0.55    inference(subsumption_resolution,[],[f229,f38])).
% 1.40/0.55  fof(f229,plain,(
% 1.40/0.55    r1_tsep_1(sK1,sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl4_15),
% 1.40/0.55    inference(resolution,[],[f219,f46])).
% 1.40/0.55  fof(f46,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f17])).
% 1.40/0.55  fof(f219,plain,(
% 1.40/0.55    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | spl4_15),
% 1.40/0.55    inference(avatar_component_clause,[],[f217])).
% 1.40/0.55  fof(f228,plain,(
% 1.40/0.55    spl4_13),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f227])).
% 1.40/0.55  fof(f227,plain,(
% 1.40/0.55    $false | spl4_13),
% 1.40/0.55    inference(subsumption_resolution,[],[f226,f29])).
% 1.40/0.55  fof(f226,plain,(
% 1.40/0.55    v2_struct_0(sK0) | spl4_13),
% 1.40/0.55    inference(subsumption_resolution,[],[f225,f31])).
% 1.40/0.55  fof(f225,plain,(
% 1.40/0.55    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_13),
% 1.40/0.55    inference(subsumption_resolution,[],[f224,f32])).
% 1.40/0.55  fof(f224,plain,(
% 1.40/0.55    v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_13),
% 1.40/0.55    inference(subsumption_resolution,[],[f223,f33])).
% 1.40/0.55  fof(f223,plain,(
% 1.40/0.55    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_13),
% 1.40/0.55    inference(subsumption_resolution,[],[f222,f34])).
% 1.40/0.55  fof(f222,plain,(
% 1.40/0.55    v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_13),
% 1.40/0.55    inference(subsumption_resolution,[],[f221,f35])).
% 1.40/0.55  fof(f221,plain,(
% 1.40/0.55    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl4_13),
% 1.40/0.55    inference(resolution,[],[f211,f54])).
% 1.40/0.55  fof(f54,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f23])).
% 1.40/0.55  fof(f211,plain,(
% 1.40/0.55    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | spl4_13),
% 1.40/0.55    inference(avatar_component_clause,[],[f209])).
% 1.40/0.55  fof(f220,plain,(
% 1.40/0.55    ~spl4_13 | spl4_14 | ~spl4_15 | spl4_2 | ~spl4_12),
% 1.40/0.55    inference(avatar_split_clause,[],[f190,f187,f60,f217,f213,f209])).
% 1.40/0.55  fof(f187,plain,(
% 1.40/0.55    spl4_12 <=> ! [X2] : (~m1_pre_topc(X2,sK1) | r1_tsep_1(sK3,X2) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0))),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.40/0.55  fof(f190,plain,(
% 1.40/0.55    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | (spl4_2 | ~spl4_12)),
% 1.40/0.55    inference(resolution,[],[f188,f62])).
% 1.40/0.55  fof(f188,plain,(
% 1.40/0.55    ( ! [X2] : (r1_tsep_1(sK3,X2) | ~m1_pre_topc(X2,sK1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0)) ) | ~spl4_12),
% 1.40/0.55    inference(avatar_component_clause,[],[f187])).
% 1.40/0.55  fof(f189,plain,(
% 1.40/0.55    spl4_11 | spl4_12 | ~spl4_5),
% 1.40/0.55    inference(avatar_split_clause,[],[f145,f73,f187,f184])).
% 1.40/0.55  fof(f73,plain,(
% 1.40/0.55    spl4_5 <=> r1_tsep_1(sK3,sK1)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.40/0.55  fof(f145,plain,(
% 1.40/0.55    ( ! [X2,X3] : (~m1_pre_topc(X2,sK1) | ~m1_pre_topc(X3,sK3) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | r1_tsep_1(sK3,X2)) ) | ~spl4_5),
% 1.40/0.55    inference(subsumption_resolution,[],[f144,f36])).
% 1.40/0.55  fof(f144,plain,(
% 1.40/0.55    ( ! [X2,X3] : (~m1_pre_topc(X2,sK1) | ~m1_pre_topc(X3,sK3) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | v2_struct_0(sK3) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | r1_tsep_1(sK3,X2)) ) | ~spl4_5),
% 1.40/0.55    inference(subsumption_resolution,[],[f143,f37])).
% 1.40/0.55  fof(f143,plain,(
% 1.40/0.55    ( ! [X2,X3] : (~m1_pre_topc(X2,sK1) | ~m1_pre_topc(X3,sK3) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | r1_tsep_1(sK3,X2)) ) | ~spl4_5),
% 1.40/0.55    inference(subsumption_resolution,[],[f142,f32])).
% 1.40/0.55  fof(f142,plain,(
% 1.40/0.55    ( ! [X2,X3] : (~m1_pre_topc(X2,sK1) | ~m1_pre_topc(X3,sK3) | v2_struct_0(sK1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | r1_tsep_1(sK3,X2)) ) | ~spl4_5),
% 1.40/0.55    inference(subsumption_resolution,[],[f137,f33])).
% 1.40/0.55  fof(f137,plain,(
% 1.40/0.55    ( ! [X2,X3] : (~m1_pre_topc(X2,sK1) | ~m1_pre_topc(X3,sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | r1_tsep_1(sK3,X2)) ) | ~spl4_5),
% 1.40/0.55    inference(resolution,[],[f135,f75])).
% 1.40/0.55  fof(f75,plain,(
% 1.40/0.55    r1_tsep_1(sK3,sK1) | ~spl4_5),
% 1.40/0.55    inference(avatar_component_clause,[],[f73])).
% 1.40/0.55  fof(f114,plain,(
% 1.40/0.55    ~spl4_4 | spl4_6 | ~spl4_8),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f113])).
% 1.40/0.55  fof(f113,plain,(
% 1.40/0.55    $false | (~spl4_4 | spl4_6 | ~spl4_8)),
% 1.40/0.55    inference(subsumption_resolution,[],[f110,f31])).
% 1.40/0.55  fof(f110,plain,(
% 1.40/0.55    ~l1_pre_topc(sK0) | (~spl4_4 | spl4_6 | ~spl4_8)),
% 1.40/0.55    inference(resolution,[],[f109,f35])).
% 1.40/0.55  fof(f109,plain,(
% 1.40/0.55    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | (~spl4_4 | spl4_6 | ~spl4_8)),
% 1.40/0.55    inference(resolution,[],[f108,f45])).
% 1.40/0.55  fof(f108,plain,(
% 1.40/0.55    ~l1_pre_topc(sK2) | (~spl4_4 | spl4_6 | ~spl4_8)),
% 1.40/0.55    inference(subsumption_resolution,[],[f107,f91])).
% 1.40/0.55  fof(f107,plain,(
% 1.40/0.55    ~l1_pre_topc(sK3) | ~l1_pre_topc(sK2) | (~spl4_4 | spl4_6)),
% 1.40/0.55    inference(subsumption_resolution,[],[f106,f78])).
% 1.40/0.55  fof(f78,plain,(
% 1.40/0.55    ~r1_tsep_1(sK3,sK2) | spl4_6),
% 1.40/0.55    inference(avatar_component_clause,[],[f77])).
% 1.40/0.55  fof(f106,plain,(
% 1.40/0.55    r1_tsep_1(sK3,sK2) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK2) | ~spl4_4),
% 1.40/0.55    inference(resolution,[],[f71,f82])).
% 1.40/0.55  fof(f71,plain,(
% 1.40/0.55    r1_tsep_1(sK2,sK3) | ~spl4_4),
% 1.40/0.55    inference(avatar_component_clause,[],[f69])).
% 1.40/0.55  fof(f69,plain,(
% 1.40/0.55    spl4_4 <=> r1_tsep_1(sK2,sK3)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.40/0.55  fof(f105,plain,(
% 1.40/0.55    spl4_8),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f104])).
% 1.40/0.55  fof(f104,plain,(
% 1.40/0.55    $false | spl4_8),
% 1.40/0.55    inference(subsumption_resolution,[],[f101,f31])).
% 1.40/0.55  fof(f101,plain,(
% 1.40/0.55    ~l1_pre_topc(sK0) | spl4_8),
% 1.40/0.55    inference(resolution,[],[f95,f37])).
% 1.40/0.55  fof(f95,plain,(
% 1.40/0.55    ( ! [X0] : (~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0)) ) | spl4_8),
% 1.40/0.55    inference(resolution,[],[f92,f45])).
% 1.40/0.55  fof(f92,plain,(
% 1.40/0.55    ~l1_pre_topc(sK3) | spl4_8),
% 1.40/0.55    inference(avatar_component_clause,[],[f90])).
% 1.40/0.55  fof(f100,plain,(
% 1.40/0.55    spl4_7),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f99])).
% 1.40/0.55  fof(f99,plain,(
% 1.40/0.55    $false | spl4_7),
% 1.40/0.55    inference(subsumption_resolution,[],[f96,f31])).
% 1.40/0.55  fof(f96,plain,(
% 1.40/0.55    ~l1_pre_topc(sK0) | spl4_7),
% 1.40/0.55    inference(resolution,[],[f94,f33])).
% 1.40/0.55  fof(f94,plain,(
% 1.40/0.55    ( ! [X0] : (~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | spl4_7),
% 1.40/0.55    inference(resolution,[],[f88,f45])).
% 1.40/0.55  fof(f88,plain,(
% 1.40/0.55    ~l1_pre_topc(sK1) | spl4_7),
% 1.40/0.55    inference(avatar_component_clause,[],[f86])).
% 1.40/0.55  fof(f93,plain,(
% 1.40/0.55    ~spl4_7 | ~spl4_8 | ~spl4_3 | spl4_5),
% 1.40/0.55    inference(avatar_split_clause,[],[f84,f73,f65,f90,f86])).
% 1.40/0.55  fof(f65,plain,(
% 1.40/0.55    spl4_3 <=> r1_tsep_1(sK1,sK3)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.40/0.55  fof(f84,plain,(
% 1.40/0.55    ~l1_pre_topc(sK3) | ~l1_pre_topc(sK1) | (~spl4_3 | spl4_5)),
% 1.40/0.55    inference(subsumption_resolution,[],[f83,f74])).
% 1.40/0.55  fof(f74,plain,(
% 1.40/0.55    ~r1_tsep_1(sK3,sK1) | spl4_5),
% 1.40/0.55    inference(avatar_component_clause,[],[f73])).
% 1.40/0.55  fof(f83,plain,(
% 1.40/0.55    r1_tsep_1(sK3,sK1) | ~l1_pre_topc(sK3) | ~l1_pre_topc(sK1) | ~spl4_3),
% 1.40/0.55    inference(resolution,[],[f82,f67])).
% 1.40/0.55  fof(f67,plain,(
% 1.40/0.55    r1_tsep_1(sK1,sK3) | ~spl4_3),
% 1.40/0.55    inference(avatar_component_clause,[],[f65])).
% 1.40/0.55  fof(f80,plain,(
% 1.40/0.55    spl4_3 | spl4_4 | spl4_5 | spl4_6),
% 1.40/0.55    inference(avatar_split_clause,[],[f42,f77,f73,f69,f65])).
% 1.40/0.55  fof(f42,plain,(
% 1.40/0.55    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1) | r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)),
% 1.40/0.55    inference(cnf_transformation,[],[f28])).
% 1.40/0.55  fof(f63,plain,(
% 1.40/0.55    ~spl4_1 | ~spl4_2),
% 1.40/0.55    inference(avatar_split_clause,[],[f39,f60,f56])).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 1.40/0.55    inference(cnf_transformation,[],[f28])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (19917)------------------------------
% 1.40/0.55  % (19917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (19917)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (19917)Memory used [KB]: 5500
% 1.40/0.55  % (19917)Time elapsed: 0.104 s
% 1.40/0.55  % (19917)------------------------------
% 1.40/0.55  % (19917)------------------------------
% 1.40/0.55  % (19916)Success in time 0.182 s
%------------------------------------------------------------------------------
