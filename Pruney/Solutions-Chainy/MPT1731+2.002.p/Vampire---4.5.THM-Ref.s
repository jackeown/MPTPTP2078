%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 889 expanded)
%              Number of leaves         :   21 ( 442 expanded)
%              Depth                    :   19
%              Number of atoms          :  892 (11555 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f230,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f130,f143,f168,f180,f191,f202,f216,f229])).

fof(f229,plain,
    ( ~ spl10_1
    | spl10_9 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl10_1
    | spl10_9 ),
    inference(subsumption_resolution,[],[f227,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sP1(sK8,sK7,sK6,sK9)
      | ( ( ~ r1_tsep_1(sK9,sK8)
          | ~ r1_tsep_1(sK9,sK7) )
        & r1_tsep_1(sK9,k1_tsep_1(sK6,sK7,sK8)) )
      | sP0(sK9,sK8,sK7,sK6)
      | sP2(sK9,sK8,sK7,sK6) )
    & m1_pre_topc(sK9,sK6)
    & ~ v2_struct_0(sK9)
    & m1_pre_topc(sK8,sK6)
    & ~ v2_struct_0(sK8)
    & m1_pre_topc(sK7,sK6)
    & ~ v2_struct_0(sK7)
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f11,f25,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( sP1(X2,X1,X0,X3)
                      | ( ( ~ r1_tsep_1(X3,X2)
                          | ~ r1_tsep_1(X3,X1) )
                        & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      | sP0(X3,X2,X1,X0)
                      | sP2(X3,X2,X1,X0) )
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
                  ( ( sP1(X2,X1,sK6,X3)
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(sK6,X1,X2)) )
                    | sP0(X3,X2,X1,sK6)
                    | sP2(X3,X2,X1,sK6) )
                  & m1_pre_topc(X3,sK6)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK6)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK6)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( sP1(X2,X1,sK6,X3)
                  | ( ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1) )
                    & r1_tsep_1(X3,k1_tsep_1(sK6,X1,X2)) )
                  | sP0(X3,X2,X1,sK6)
                  | sP2(X3,X2,X1,sK6) )
                & m1_pre_topc(X3,sK6)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK6)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK6)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( sP1(X2,sK7,sK6,X3)
                | ( ( ~ r1_tsep_1(X3,X2)
                    | ~ r1_tsep_1(X3,sK7) )
                  & r1_tsep_1(X3,k1_tsep_1(sK6,sK7,X2)) )
                | sP0(X3,X2,sK7,sK6)
                | sP2(X3,X2,sK7,sK6) )
              & m1_pre_topc(X3,sK6)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK6)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK7,sK6)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( sP1(X2,sK7,sK6,X3)
              | ( ( ~ r1_tsep_1(X3,X2)
                  | ~ r1_tsep_1(X3,sK7) )
                & r1_tsep_1(X3,k1_tsep_1(sK6,sK7,X2)) )
              | sP0(X3,X2,sK7,sK6)
              | sP2(X3,X2,sK7,sK6) )
            & m1_pre_topc(X3,sK6)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK6)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( sP1(sK8,sK7,sK6,X3)
            | ( ( ~ r1_tsep_1(X3,sK8)
                | ~ r1_tsep_1(X3,sK7) )
              & r1_tsep_1(X3,k1_tsep_1(sK6,sK7,sK8)) )
            | sP0(X3,sK8,sK7,sK6)
            | sP2(X3,sK8,sK7,sK6) )
          & m1_pre_topc(X3,sK6)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK8,sK6)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X3] :
        ( ( sP1(sK8,sK7,sK6,X3)
          | ( ( ~ r1_tsep_1(X3,sK8)
              | ~ r1_tsep_1(X3,sK7) )
            & r1_tsep_1(X3,k1_tsep_1(sK6,sK7,sK8)) )
          | sP0(X3,sK8,sK7,sK6)
          | sP2(X3,sK8,sK7,sK6) )
        & m1_pre_topc(X3,sK6)
        & ~ v2_struct_0(X3) )
   => ( ( sP1(sK8,sK7,sK6,sK9)
        | ( ( ~ r1_tsep_1(sK9,sK8)
            | ~ r1_tsep_1(sK9,sK7) )
          & r1_tsep_1(sK9,k1_tsep_1(sK6,sK7,sK8)) )
        | sP0(sK9,sK8,sK7,sK6)
        | sP2(sK9,sK8,sK7,sK6) )
      & m1_pre_topc(sK9,sK6)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( sP1(X2,X1,X0,X3)
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | sP0(X3,X2,X1,X0)
                    | sP2(X3,X2,X1,X0) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f5,f10,f9,f8])).

fof(f8,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
        & r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f9,plain,(
    ! [X2,X1,X0,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
        & r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f10,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( ~ r1_tsep_1(X2,X3)
          | ~ r1_tsep_1(X1,X3) )
        & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
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
                   => ( ( ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                       => ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) ) )
                      & ( ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                      & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                       => ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
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
                 => ( ( ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) )
                     => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                     => ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) )
                     => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                    & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                     => ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tmap_1)).

fof(f227,plain,
    ( v2_struct_0(sK9)
    | ~ spl10_1
    | spl10_9 ),
    inference(subsumption_resolution,[],[f226,f190])).

fof(f190,plain,
    ( ~ r1_tsep_1(sK7,sK9)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl10_9
  <=> r1_tsep_1(sK7,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f226,plain,
    ( r1_tsep_1(sK7,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f225,f49])).

fof(f49,plain,(
    m1_pre_topc(sK9,sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f225,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK7,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f224,f41])).

fof(f41,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f224,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK7,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f223,f42])).

fof(f42,plain,(
    v2_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f223,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK7,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f222,f43])).

fof(f43,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f222,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK7,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f221,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f26])).

fof(f221,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK7,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f220,f45])).

fof(f45,plain,(
    m1_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f220,plain,
    ( ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK7,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f219,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f26])).

fof(f219,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK7,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f218,f47])).

fof(f47,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f218,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK7,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(resolution,[],[f119,f64])).

fof(f64,plain,
    ( sP2(sK9,sK8,sK7,sK6)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl10_1
  <=> sP2(sK9,sK8,sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f119,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP2(X4,X5,X7,X6)
      | ~ m1_pre_topc(X5,X6)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X7,X6)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X4,X6)
      | r1_tsep_1(X7,X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f115,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X1,X2,X0,X3)
      | r1_tsep_1(X0,X1)
      | ~ sP2(X1,X2,X0,X3) ) ),
    inference(resolution,[],[f58,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ~ r1_tsep_1(X1,X0)
          | ~ r1_tsep_1(X2,X0) )
        & r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( ~ r1_tsep_1(X2,X3)
          | ~ r1_tsep_1(X1,X3) )
        & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | r1_tsep_1(X2,X0)
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | ( r1_tsep_1(X1,X0)
        & r1_tsep_1(X2,X0) )
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
      | ( r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3) )
      | ~ sP3(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X3,X2,X1,X0] :
      ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
      | ( r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3) )
      | ~ sP3(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f115,plain,(
    ! [X14,X12,X15,X13] :
      ( sP3(X12,X14,X15,X13)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X14,X13)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X15,X13)
      | v2_struct_0(X15)
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13)
      | ~ m1_pre_topc(X12,X13) ) ),
    inference(resolution,[],[f60,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X0,X1,X2,X3)
      | sP3(X0,X3,X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP4(X3,X2,X1,X0)
        & ( ~ r1_tsep_1(X0,X3)
          | ~ r1_tsep_1(X0,X2)
          | r1_tsep_1(X0,k1_tsep_1(X1,X2,X3)) )
        & sP3(X0,X3,X2,X1)
        & ( ~ r1_tsep_1(X3,X0)
          | ~ r1_tsep_1(X2,X0)
          | r1_tsep_1(k1_tsep_1(X1,X2,X3),X0) ) )
      | ~ sP5(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X3,X0,X1,X2] :
      ( ( sP4(X2,X1,X0,X3)
        & ( ~ r1_tsep_1(X3,X2)
          | ~ r1_tsep_1(X3,X1)
          | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
        & sP3(X3,X2,X1,X0)
        & ( ~ r1_tsep_1(X2,X3)
          | ~ r1_tsep_1(X1,X3)
          | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
      | ~ sP5(X3,X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X3,X0,X1,X2] :
      ( ( sP4(X2,X1,X0,X3)
        & ( ~ r1_tsep_1(X3,X2)
          | ~ r1_tsep_1(X3,X1)
          | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
        & sP3(X3,X2,X1,X0)
        & ( ~ r1_tsep_1(X2,X3)
          | ~ r1_tsep_1(X1,X3)
          | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
      | ~ sP5(X3,X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X0,X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP5(X3,X0,X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f7,f14,f13,f12])).

fof(f13,plain,(
    ! [X2,X1,X0,X3] :
      ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
      | ( r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1) )
      | ~ sP4(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      | ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1)
                      | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) )
                    & ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(X1,X3)
                      | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      | ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1)
                      | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) )
                    & ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(X1,X3)
                      | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
                 => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ~ ( r1_tsep_1(X3,X2)
                            & r1_tsep_1(X3,X1) ) )
                    & ~ ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1)
                        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & ~ ( r1_tsep_1(X2,X3)
                            & r1_tsep_1(X1,X3) ) )
                    & ~ ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3)
                        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tmap_1)).

fof(f216,plain,
    ( ~ spl10_1
    | spl10_8 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl10_1
    | spl10_8 ),
    inference(subsumption_resolution,[],[f214,f48])).

fof(f214,plain,
    ( v2_struct_0(sK9)
    | ~ spl10_1
    | spl10_8 ),
    inference(subsumption_resolution,[],[f213,f186])).

fof(f186,plain,
    ( ~ r1_tsep_1(sK8,sK9)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl10_8
  <=> r1_tsep_1(sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f213,plain,
    ( r1_tsep_1(sK8,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f212,f49])).

fof(f212,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK8,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f211,f41])).

fof(f211,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK8,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f210,f42])).

fof(f210,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK8,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f209,f43])).

fof(f209,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK8,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f208,f44])).

fof(f208,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK8,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f207,f45])).

fof(f207,plain,
    ( ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK8,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f206,f46])).

fof(f206,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK8,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f205,f47])).

fof(f205,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | r1_tsep_1(sK8,sK9)
    | v2_struct_0(sK9)
    | ~ spl10_1 ),
    inference(resolution,[],[f118,f64])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X3,X2)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X0,X2)
      | r1_tsep_1(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f115,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X1,X0,X2,X3)
      | r1_tsep_1(X0,X1)
      | ~ sP2(X1,X0,X2,X3) ) ),
    inference(resolution,[],[f59,f33])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | r1_tsep_1(X1,X0)
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f202,plain,(
    spl10_7 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl10_7 ),
    inference(subsumption_resolution,[],[f200,f49])).

fof(f200,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f199,f41])).

fof(f199,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f198,f42])).

fof(f198,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f197,f43])).

fof(f197,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f196,f44])).

fof(f196,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f195,f45])).

fof(f195,plain,
    ( ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f194,f46])).

fof(f194,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f193,f47])).

fof(f193,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | spl10_7 ),
    inference(subsumption_resolution,[],[f192,f48])).

fof(f192,plain,
    ( v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | spl10_7 ),
    inference(resolution,[],[f167,f114])).

fof(f114,plain,(
    ! [X10,X8,X11,X9] :
      ( sP4(X10,X11,X9,X8)
      | v2_struct_0(X8)
      | ~ m1_pre_topc(X10,X9)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X11,X9)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | ~ m1_pre_topc(X8,X9) ) ),
    inference(resolution,[],[f60,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X0,X1,X2,X3)
      | sP4(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f167,plain,
    ( ~ sP4(sK8,sK7,sK6,sK9)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl10_7
  <=> sP4(sK8,sK7,sK6,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f191,plain,
    ( ~ spl10_8
    | ~ spl10_9
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f182,f62,f188,f184])).

fof(f182,plain,
    ( ~ r1_tsep_1(sK7,sK9)
    | ~ r1_tsep_1(sK8,sK9)
    | ~ spl10_1 ),
    inference(resolution,[],[f64,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ r1_tsep_1(X2,X0)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f180,plain,
    ( ~ spl10_7
    | spl10_3
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f149,f83,f70,f165])).

fof(f70,plain,
    ( spl10_3
  <=> r1_tsep_1(sK9,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f83,plain,
    ( spl10_6
  <=> r1_tsep_1(sK9,k1_tsep_1(sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f149,plain,
    ( r1_tsep_1(sK9,sK7)
    | ~ sP4(sK8,sK7,sK6,sK9)
    | ~ spl10_6 ),
    inference(resolution,[],[f85,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0))
      | r1_tsep_1(X3,X1)
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0))
      | ( r1_tsep_1(X3,X0)
        & r1_tsep_1(X3,X1) )
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0,X3] :
      ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
      | ( r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1) )
      | ~ sP4(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f85,plain,
    ( r1_tsep_1(sK9,k1_tsep_1(sK6,sK7,sK8))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f168,plain,
    ( ~ spl10_7
    | spl10_4
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f148,f83,f74,f165])).

fof(f74,plain,
    ( spl10_4
  <=> r1_tsep_1(sK9,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f148,plain,
    ( r1_tsep_1(sK9,sK8)
    | ~ sP4(sK8,sK7,sK6,sK9)
    | ~ spl10_6 ),
    inference(resolution,[],[f85,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0))
      | r1_tsep_1(X3,X0)
      | ~ sP4(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f143,plain,(
    ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f141,f49])).

fof(f141,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f140,f41])).

fof(f140,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f139,f42])).

fof(f139,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f138,f43])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f137,f44])).

fof(f137,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f136,f45])).

fof(f136,plain,
    ( ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f135,f46])).

fof(f135,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f134,f47])).

fof(f134,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f131,f48])).

fof(f131,plain,
    ( v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_5 ),
    inference(resolution,[],[f80,f112])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X2,X3,X1,X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f60,f111])).

fof(f111,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ sP5(X8,X11,X9,X10)
      | ~ sP1(X10,X9,X11,X8) ) ),
    inference(subsumption_resolution,[],[f110,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_tsep_1(X3,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0))
        & r1_tsep_1(X3,X0)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X2,X1,X0,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
        & r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f110,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_tsep_1(X8,X10)
      | ~ sP5(X8,X11,X9,X10)
      | ~ sP1(X10,X9,X11,X8) ) ),
    inference(subsumption_resolution,[],[f106,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_tsep_1(X3,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f106,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_tsep_1(X8,X9)
      | ~ r1_tsep_1(X8,X10)
      | ~ sP5(X8,X11,X9,X10)
      | ~ sP1(X10,X9,X11,X8) ) ),
    inference(resolution,[],[f54,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))
      | ~ r1_tsep_1(X0,X2)
      | ~ r1_tsep_1(X0,X3)
      | ~ sP5(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,
    ( sP1(sK8,sK7,sK6,sK9)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl10_5
  <=> sP1(sK8,sK7,sK6,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f130,plain,(
    ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f128,f49])).

fof(f128,plain,
    ( ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f127,f41])).

fof(f127,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f126,f42])).

fof(f126,plain,
    ( ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f125,f43])).

fof(f125,plain,
    ( ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f124,f44])).

fof(f124,plain,
    ( v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f123,f45])).

fof(f123,plain,
    ( ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f122,f46])).

fof(f122,plain,
    ( v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f121,f47])).

fof(f121,plain,
    ( ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f120,f48])).

fof(f120,plain,
    ( v2_struct_0(sK9)
    | ~ m1_pre_topc(sK8,sK6)
    | v2_struct_0(sK8)
    | ~ m1_pre_topc(sK7,sK6)
    | v2_struct_0(sK7)
    | ~ l1_pre_topc(sK6)
    | ~ v2_pre_topc(sK6)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK9,sK6)
    | ~ spl10_2 ),
    inference(resolution,[],[f113,f68])).

fof(f68,plain,
    ( sP0(sK9,sK8,sK7,sK6)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl10_2
  <=> sP0(sK9,sK8,sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f113,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP0(X4,X6,X7,X5)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X6,X5)
      | v2_struct_0(X6)
      | ~ m1_pre_topc(X7,X5)
      | v2_struct_0(X7)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,X5) ) ),
    inference(resolution,[],[f60,f102])).

fof(f102,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ sP5(X9,X11,X8,X10)
      | ~ sP0(X9,X10,X8,X11) ) ),
    inference(subsumption_resolution,[],[f101,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
        & r1_tsep_1(X1,X0)
        & r1_tsep_1(X2,X0) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
        & r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f8])).

% (15897)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f101,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_tsep_1(X10,X9)
      | ~ sP5(X9,X11,X8,X10)
      | ~ sP0(X9,X10,X8,X11) ) ),
    inference(subsumption_resolution,[],[f97,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f97,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_tsep_1(X8,X9)
      | ~ r1_tsep_1(X10,X9)
      | ~ sP5(X9,X11,X8,X10)
      | ~ sP0(X9,X10,X8,X11) ) ),
    inference(resolution,[],[f52,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(k1_tsep_1(X1,X2,X3),X0)
      | ~ r1_tsep_1(X2,X0)
      | ~ r1_tsep_1(X3,X0)
      | ~ sP5(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,
    ( spl10_1
    | spl10_2
    | spl10_6
    | spl10_5 ),
    inference(avatar_split_clause,[],[f50,f78,f83,f66,f62])).

fof(f50,plain,
    ( sP1(sK8,sK7,sK6,sK9)
    | r1_tsep_1(sK9,k1_tsep_1(sK6,sK7,sK8))
    | sP0(sK9,sK8,sK7,sK6)
    | sP2(sK9,sK8,sK7,sK6) ),
    inference(cnf_transformation,[],[f26])).

fof(f81,plain,
    ( spl10_1
    | spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | spl10_5 ),
    inference(avatar_split_clause,[],[f51,f78,f74,f70,f66,f62])).

fof(f51,plain,
    ( sP1(sK8,sK7,sK6,sK9)
    | ~ r1_tsep_1(sK9,sK8)
    | ~ r1_tsep_1(sK9,sK7)
    | sP0(sK9,sK8,sK7,sK6)
    | sP2(sK9,sK8,sK7,sK6) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:44:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (15890)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.46  % (15886)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.47  % (15899)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.22/0.47  % (15891)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.22/0.47  % (15899)Refutation not found, incomplete strategy% (15899)------------------------------
% 0.22/0.47  % (15899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (15899)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (15899)Memory used [KB]: 895
% 0.22/0.47  % (15899)Time elapsed: 0.006 s
% 0.22/0.47  % (15899)------------------------------
% 0.22/0.47  % (15899)------------------------------
% 0.22/0.48  % (15891)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f230,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f81,f86,f130,f143,f168,f180,f191,f202,f216,f229])).
% 0.22/0.48  fof(f229,plain,(
% 0.22/0.48    ~spl10_1 | spl10_9),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f228])).
% 0.22/0.48  fof(f228,plain,(
% 0.22/0.48    $false | (~spl10_1 | spl10_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f227,f48])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ~v2_struct_0(sK9)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ((((sP1(sK8,sK7,sK6,sK9) | ((~r1_tsep_1(sK9,sK8) | ~r1_tsep_1(sK9,sK7)) & r1_tsep_1(sK9,k1_tsep_1(sK6,sK7,sK8))) | sP0(sK9,sK8,sK7,sK6) | sP2(sK9,sK8,sK7,sK6)) & m1_pre_topc(sK9,sK6) & ~v2_struct_0(sK9)) & m1_pre_topc(sK8,sK6) & ~v2_struct_0(sK8)) & m1_pre_topc(sK7,sK6) & ~v2_struct_0(sK7)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f11,f25,f24,f23,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,X0,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0) | sP2(X3,X2,X1,X0)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,sK6,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(sK6,X1,X2))) | sP0(X3,X2,X1,sK6) | sP2(X3,X2,X1,sK6)) & m1_pre_topc(X3,sK6) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK6) & ~v2_struct_0(X1)) & l1_pre_topc(sK6) & v2_pre_topc(sK6) & ~v2_struct_0(sK6))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,sK6,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(sK6,X1,X2))) | sP0(X3,X2,X1,sK6) | sP2(X3,X2,X1,sK6)) & m1_pre_topc(X3,sK6) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK6) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((sP1(X2,sK7,sK6,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,sK7)) & r1_tsep_1(X3,k1_tsep_1(sK6,sK7,X2))) | sP0(X3,X2,sK7,sK6) | sP2(X3,X2,sK7,sK6)) & m1_pre_topc(X3,sK6) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) & m1_pre_topc(sK7,sK6) & ~v2_struct_0(sK7))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ? [X2] : (? [X3] : ((sP1(X2,sK7,sK6,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,sK7)) & r1_tsep_1(X3,k1_tsep_1(sK6,sK7,X2))) | sP0(X3,X2,sK7,sK6) | sP2(X3,X2,sK7,sK6)) & m1_pre_topc(X3,sK6) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK6) & ~v2_struct_0(X2)) => (? [X3] : ((sP1(sK8,sK7,sK6,X3) | ((~r1_tsep_1(X3,sK8) | ~r1_tsep_1(X3,sK7)) & r1_tsep_1(X3,k1_tsep_1(sK6,sK7,sK8))) | sP0(X3,sK8,sK7,sK6) | sP2(X3,sK8,sK7,sK6)) & m1_pre_topc(X3,sK6) & ~v2_struct_0(X3)) & m1_pre_topc(sK8,sK6) & ~v2_struct_0(sK8))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ? [X3] : ((sP1(sK8,sK7,sK6,X3) | ((~r1_tsep_1(X3,sK8) | ~r1_tsep_1(X3,sK7)) & r1_tsep_1(X3,k1_tsep_1(sK6,sK7,sK8))) | sP0(X3,sK8,sK7,sK6) | sP2(X3,sK8,sK7,sK6)) & m1_pre_topc(X3,sK6) & ~v2_struct_0(X3)) => ((sP1(sK8,sK7,sK6,sK9) | ((~r1_tsep_1(sK9,sK8) | ~r1_tsep_1(sK9,sK7)) & r1_tsep_1(sK9,k1_tsep_1(sK6,sK7,sK8))) | sP0(sK9,sK8,sK7,sK6) | sP2(sK9,sK8,sK7,sK6)) & m1_pre_topc(sK9,sK6) & ~v2_struct_0(sK9))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,X0,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0) | sP2(X3,X2,X1,X0)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(definition_folding,[],[f5,f10,f9,f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X3,X2,X1,X0] : ((~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) | ~sP0(X3,X2,X1,X0))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X2,X1,X0,X3] : ((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) | ~sP1(X2,X1,X0,X3))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X3,X2,X1,X0] : (((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) | ~sP2(X3,X2,X1,X0))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.48  fof(f5,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f4])).
% 0.22/0.48  fof(f4,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (((r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) => (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ((r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) & (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) => (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f2])).
% 0.22/0.48  fof(f2,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (((r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) => (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ((r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) & (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) => (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tmap_1)).
% 0.22/0.48  fof(f227,plain,(
% 0.22/0.48    v2_struct_0(sK9) | (~spl10_1 | spl10_9)),
% 0.22/0.48    inference(subsumption_resolution,[],[f226,f190])).
% 0.22/0.48  fof(f190,plain,(
% 0.22/0.48    ~r1_tsep_1(sK7,sK9) | spl10_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f188])).
% 0.22/0.48  fof(f188,plain,(
% 0.22/0.48    spl10_9 <=> r1_tsep_1(sK7,sK9)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.22/0.48  fof(f226,plain,(
% 0.22/0.48    r1_tsep_1(sK7,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f225,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    m1_pre_topc(sK9,sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f225,plain,(
% 0.22/0.48    ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK7,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f224,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ~v2_struct_0(sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f224,plain,(
% 0.22/0.48    v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK7,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f223,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    v2_pre_topc(sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f223,plain,(
% 0.22/0.48    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK7,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f222,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    l1_pre_topc(sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f222,plain,(
% 0.22/0.48    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK7,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f221,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ~v2_struct_0(sK7)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f221,plain,(
% 0.22/0.48    v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK7,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f220,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    m1_pre_topc(sK7,sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f220,plain,(
% 0.22/0.48    ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK7,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f219,f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ~v2_struct_0(sK8)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f219,plain,(
% 0.22/0.48    v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK7,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f218,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    m1_pre_topc(sK8,sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f218,plain,(
% 0.22/0.48    ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK7,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(resolution,[],[f119,f64])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    sP2(sK9,sK8,sK7,sK6) | ~spl10_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl10_1 <=> sP2(sK9,sK8,sK7,sK6)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ( ! [X6,X4,X7,X5] : (~sP2(X4,X5,X7,X6) | ~m1_pre_topc(X5,X6) | v2_struct_0(X5) | ~m1_pre_topc(X7,X6) | v2_struct_0(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6) | ~m1_pre_topc(X4,X6) | r1_tsep_1(X7,X4) | v2_struct_0(X4)) )),
% 0.22/0.48    inference(resolution,[],[f115,f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~sP3(X1,X2,X0,X3) | r1_tsep_1(X0,X1) | ~sP2(X1,X2,X0,X3)) )),
% 0.22/0.48    inference(resolution,[],[f58,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) | ~sP2(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (((~r1_tsep_1(X1,X0) | ~r1_tsep_1(X2,X0)) & r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)) | ~sP2(X0,X1,X2,X3))),
% 0.22/0.48    inference(rectify,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X3,X2,X1,X0] : (((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) | ~sP2(X3,X2,X1,X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f10])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) | r1_tsep_1(X2,X0) | ~sP3(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (~r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) | (r1_tsep_1(X1,X0) & r1_tsep_1(X2,X0)) | ~sP3(X0,X1,X2,X3))),
% 0.22/0.48    inference(rectify,[],[f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ! [X3,X2,X1,X0] : (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) | ~sP3(X3,X2,X1,X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X3,X2,X1,X0] : (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) | ~sP3(X3,X2,X1,X0))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.48  fof(f115,plain,(
% 0.22/0.48    ( ! [X14,X12,X15,X13] : (sP3(X12,X14,X15,X13) | v2_struct_0(X12) | ~m1_pre_topc(X14,X13) | v2_struct_0(X14) | ~m1_pre_topc(X15,X13) | v2_struct_0(X15) | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | v2_struct_0(X13) | ~m1_pre_topc(X12,X13)) )),
% 0.22/0.48    inference(resolution,[],[f60,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~sP5(X0,X1,X2,X3) | sP3(X0,X3,X2,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((sP4(X3,X2,X1,X0) & (~r1_tsep_1(X0,X3) | ~r1_tsep_1(X0,X2) | r1_tsep_1(X0,k1_tsep_1(X1,X2,X3))) & sP3(X0,X3,X2,X1) & (~r1_tsep_1(X3,X0) | ~r1_tsep_1(X2,X0) | r1_tsep_1(k1_tsep_1(X1,X2,X3),X0))) | ~sP5(X0,X1,X2,X3))),
% 0.22/0.48    inference(rectify,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X3,X0,X1,X2] : ((sP4(X2,X1,X0,X3) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1) | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & sP3(X3,X2,X1,X0) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3) | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) | ~sP5(X3,X0,X1,X2))),
% 0.22/0.48    inference(nnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X3,X0,X1,X2] : ((sP4(X2,X1,X0,X3) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1) | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & sP3(X3,X2,X1,X0) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3) | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) | ~sP5(X3,X0,X1,X2))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (sP5(X3,X0,X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP5(X3,X0,X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(definition_folding,[],[f7,f14,f13,f12])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X2,X1,X0,X3] : (~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) | ~sP4(X2,X1,X0,X3))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1) | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3) | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1) | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3) | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~(r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & ~(r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)))))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tmap_1)).
% 0.22/0.48  fof(f216,plain,(
% 0.22/0.48    ~spl10_1 | spl10_8),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f215])).
% 0.22/0.48  fof(f215,plain,(
% 0.22/0.48    $false | (~spl10_1 | spl10_8)),
% 0.22/0.48    inference(subsumption_resolution,[],[f214,f48])).
% 0.22/0.48  fof(f214,plain,(
% 0.22/0.48    v2_struct_0(sK9) | (~spl10_1 | spl10_8)),
% 0.22/0.48    inference(subsumption_resolution,[],[f213,f186])).
% 0.22/0.48  fof(f186,plain,(
% 0.22/0.48    ~r1_tsep_1(sK8,sK9) | spl10_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f184])).
% 0.22/0.48  fof(f184,plain,(
% 0.22/0.48    spl10_8 <=> r1_tsep_1(sK8,sK9)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.22/0.48  fof(f213,plain,(
% 0.22/0.48    r1_tsep_1(sK8,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f212,f49])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK8,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f211,f41])).
% 0.22/0.48  fof(f211,plain,(
% 0.22/0.48    v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK8,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f210,f42])).
% 0.22/0.48  fof(f210,plain,(
% 0.22/0.48    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK8,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f209,f43])).
% 0.22/0.48  fof(f209,plain,(
% 0.22/0.48    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK8,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f208,f44])).
% 0.22/0.48  fof(f208,plain,(
% 0.22/0.48    v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK8,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f207,f45])).
% 0.22/0.48  fof(f207,plain,(
% 0.22/0.48    ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK8,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f206,f46])).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK8,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f205,f47])).
% 0.22/0.48  fof(f205,plain,(
% 0.22/0.48    ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | r1_tsep_1(sK8,sK9) | v2_struct_0(sK9) | ~spl10_1),
% 0.22/0.48    inference(resolution,[],[f118,f64])).
% 0.22/0.48  fof(f118,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X3,X2) | ~m1_pre_topc(X1,X2) | v2_struct_0(X1) | ~m1_pre_topc(X3,X2) | v2_struct_0(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~m1_pre_topc(X0,X2) | r1_tsep_1(X1,X0) | v2_struct_0(X0)) )),
% 0.22/0.48    inference(resolution,[],[f115,f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~sP3(X1,X0,X2,X3) | r1_tsep_1(X0,X1) | ~sP2(X1,X0,X2,X3)) )),
% 0.22/0.48    inference(resolution,[],[f59,f33])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) | r1_tsep_1(X1,X0) | ~sP3(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    spl10_7),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f201])).
% 0.22/0.48  fof(f201,plain,(
% 0.22/0.48    $false | spl10_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f200,f49])).
% 0.22/0.48  fof(f200,plain,(
% 0.22/0.48    ~m1_pre_topc(sK9,sK6) | spl10_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f199,f41])).
% 0.22/0.48  fof(f199,plain,(
% 0.22/0.48    v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | spl10_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f198,f42])).
% 0.22/0.48  fof(f198,plain,(
% 0.22/0.48    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | spl10_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f197,f43])).
% 0.22/0.48  fof(f197,plain,(
% 0.22/0.48    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | spl10_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f196,f44])).
% 0.22/0.48  fof(f196,plain,(
% 0.22/0.48    v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | spl10_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f195,f45])).
% 0.22/0.48  fof(f195,plain,(
% 0.22/0.48    ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | spl10_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f194,f46])).
% 0.22/0.48  fof(f194,plain,(
% 0.22/0.48    v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | spl10_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f193,f47])).
% 0.22/0.48  fof(f193,plain,(
% 0.22/0.48    ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | spl10_7),
% 0.22/0.48    inference(subsumption_resolution,[],[f192,f48])).
% 0.22/0.48  fof(f192,plain,(
% 0.22/0.48    v2_struct_0(sK9) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | spl10_7),
% 0.22/0.48    inference(resolution,[],[f167,f114])).
% 0.22/0.48  fof(f114,plain,(
% 0.22/0.48    ( ! [X10,X8,X11,X9] : (sP4(X10,X11,X9,X8) | v2_struct_0(X8) | ~m1_pre_topc(X10,X9) | v2_struct_0(X10) | ~m1_pre_topc(X11,X9) | v2_struct_0(X11) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | v2_struct_0(X9) | ~m1_pre_topc(X8,X9)) )),
% 0.22/0.48    inference(resolution,[],[f60,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~sP5(X0,X1,X2,X3) | sP4(X3,X2,X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f167,plain,(
% 0.22/0.48    ~sP4(sK8,sK7,sK6,sK9) | spl10_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f165])).
% 0.22/0.48  fof(f165,plain,(
% 0.22/0.48    spl10_7 <=> sP4(sK8,sK7,sK6,sK9)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.22/0.48  fof(f191,plain,(
% 0.22/0.48    ~spl10_8 | ~spl10_9 | ~spl10_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f182,f62,f188,f184])).
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    ~r1_tsep_1(sK7,sK9) | ~r1_tsep_1(sK8,sK9) | ~spl10_1),
% 0.22/0.48    inference(resolution,[],[f64,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X2,X3) | ~r1_tsep_1(X2,X0) | ~r1_tsep_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f180,plain,(
% 0.22/0.48    ~spl10_7 | spl10_3 | ~spl10_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f149,f83,f70,f165])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    spl10_3 <=> r1_tsep_1(sK9,sK7)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    spl10_6 <=> r1_tsep_1(sK9,k1_tsep_1(sK6,sK7,sK8))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    r1_tsep_1(sK9,sK7) | ~sP4(sK8,sK7,sK6,sK9) | ~spl10_6),
% 0.22/0.48    inference(resolution,[],[f85,f56])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,k1_tsep_1(X2,X1,X0)) | r1_tsep_1(X3,X1) | ~sP4(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : (~r1_tsep_1(X3,k1_tsep_1(X2,X1,X0)) | (r1_tsep_1(X3,X0) & r1_tsep_1(X3,X1)) | ~sP4(X0,X1,X2,X3))),
% 0.22/0.48    inference(rectify,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X2,X1,X0,X3] : (~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) | ~sP4(X2,X1,X0,X3))),
% 0.22/0.48    inference(nnf_transformation,[],[f13])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    r1_tsep_1(sK9,k1_tsep_1(sK6,sK7,sK8)) | ~spl10_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f83])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    ~spl10_7 | spl10_4 | ~spl10_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f148,f83,f74,f165])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl10_4 <=> r1_tsep_1(sK9,sK8)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    r1_tsep_1(sK9,sK8) | ~sP4(sK8,sK7,sK6,sK9) | ~spl10_6),
% 0.22/0.48    inference(resolution,[],[f85,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,k1_tsep_1(X2,X1,X0)) | r1_tsep_1(X3,X0) | ~sP4(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    ~spl10_5),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f142])).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    $false | ~spl10_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f141,f49])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ~m1_pre_topc(sK9,sK6) | ~spl10_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f140,f41])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f139,f42])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f138,f43])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f137,f44])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f136,f45])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f135,f46])).
% 0.22/0.48  fof(f135,plain,(
% 0.22/0.48    v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f134,f47])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_5),
% 0.22/0.48    inference(subsumption_resolution,[],[f131,f48])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    v2_struct_0(sK9) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_5),
% 0.22/0.48    inference(resolution,[],[f80,f112])).
% 0.22/0.48  fof(f112,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~sP1(X2,X3,X1,X0) | v2_struct_0(X0) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.48    inference(resolution,[],[f60,f111])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ( ! [X10,X8,X11,X9] : (~sP5(X8,X11,X9,X10) | ~sP1(X10,X9,X11,X8)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f110,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | r1_tsep_1(X3,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((~r1_tsep_1(X3,k1_tsep_1(X2,X1,X0)) & r1_tsep_1(X3,X0) & r1_tsep_1(X3,X1)) | ~sP1(X0,X1,X2,X3))),
% 0.22/0.48    inference(rectify,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X2,X1,X0,X3] : ((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) | ~sP1(X2,X1,X0,X3))),
% 0.22/0.48    inference(nnf_transformation,[],[f9])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    ( ! [X10,X8,X11,X9] : (~r1_tsep_1(X8,X10) | ~sP5(X8,X11,X9,X10) | ~sP1(X10,X9,X11,X8)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f106,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | r1_tsep_1(X3,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    ( ! [X10,X8,X11,X9] : (~r1_tsep_1(X8,X9) | ~r1_tsep_1(X8,X10) | ~sP5(X8,X11,X9,X10) | ~sP1(X10,X9,X11,X8)) )),
% 0.22/0.48    inference(resolution,[],[f54,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,k1_tsep_1(X2,X1,X0)) | ~sP1(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X0,k1_tsep_1(X1,X2,X3)) | ~r1_tsep_1(X0,X2) | ~r1_tsep_1(X0,X3) | ~sP5(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    sP1(sK8,sK7,sK6,sK9) | ~spl10_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl10_5 <=> sP1(sK8,sK7,sK6,sK9)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    ~spl10_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f129])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    $false | ~spl10_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f128,f49])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    ~m1_pre_topc(sK9,sK6) | ~spl10_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f127,f41])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f126,f42])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f125,f43])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f124,f44])).
% 0.22/0.48  fof(f124,plain,(
% 0.22/0.48    v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f123,f45])).
% 0.22/0.48  fof(f123,plain,(
% 0.22/0.48    ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f122,f46])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f121,f47])).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f120,f48])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    v2_struct_0(sK9) | ~m1_pre_topc(sK8,sK6) | v2_struct_0(sK8) | ~m1_pre_topc(sK7,sK6) | v2_struct_0(sK7) | ~l1_pre_topc(sK6) | ~v2_pre_topc(sK6) | v2_struct_0(sK6) | ~m1_pre_topc(sK9,sK6) | ~spl10_2),
% 0.22/0.48    inference(resolution,[],[f113,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    sP0(sK9,sK8,sK7,sK6) | ~spl10_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl10_2 <=> sP0(sK9,sK8,sK7,sK6)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    ( ! [X6,X4,X7,X5] : (~sP0(X4,X6,X7,X5) | v2_struct_0(X4) | ~m1_pre_topc(X6,X5) | v2_struct_0(X6) | ~m1_pre_topc(X7,X5) | v2_struct_0(X7) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~m1_pre_topc(X4,X5)) )),
% 0.22/0.48    inference(resolution,[],[f60,f102])).
% 0.22/0.48  fof(f102,plain,(
% 0.22/0.48    ( ! [X10,X8,X11,X9] : (~sP5(X9,X11,X8,X10) | ~sP0(X9,X10,X8,X11)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f101,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_tsep_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2,X3] : ((~r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) & r1_tsep_1(X1,X0) & r1_tsep_1(X2,X0)) | ~sP0(X0,X1,X2,X3))),
% 0.22/0.48    inference(rectify,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X3,X2,X1,X0] : ((~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) | ~sP0(X3,X2,X1,X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f8])).
% 0.22/0.48  % (15897)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ( ! [X10,X8,X11,X9] : (~r1_tsep_1(X10,X9) | ~sP5(X9,X11,X8,X10) | ~sP0(X9,X10,X8,X11)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f97,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_tsep_1(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ( ! [X10,X8,X11,X9] : (~r1_tsep_1(X8,X9) | ~r1_tsep_1(X10,X9) | ~sP5(X9,X11,X8,X10) | ~sP0(X9,X10,X8,X11)) )),
% 0.22/0.48    inference(resolution,[],[f52,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (r1_tsep_1(k1_tsep_1(X1,X2,X3),X0) | ~r1_tsep_1(X2,X0) | ~r1_tsep_1(X3,X0) | ~sP5(X0,X1,X2,X3)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl10_1 | spl10_2 | spl10_6 | spl10_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f50,f78,f83,f66,f62])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    sP1(sK8,sK7,sK6,sK9) | r1_tsep_1(sK9,k1_tsep_1(sK6,sK7,sK8)) | sP0(sK9,sK8,sK7,sK6) | sP2(sK9,sK8,sK7,sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl10_1 | spl10_2 | ~spl10_3 | ~spl10_4 | spl10_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f51,f78,f74,f70,f66,f62])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    sP1(sK8,sK7,sK6,sK9) | ~r1_tsep_1(sK9,sK8) | ~r1_tsep_1(sK9,sK7) | sP0(sK9,sK8,sK7,sK6) | sP2(sK9,sK8,sK7,sK6)),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (15891)------------------------------
% 0.22/0.48  % (15891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (15891)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (15891)Memory used [KB]: 5500
% 0.22/0.48  % (15891)Time elapsed: 0.012 s
% 0.22/0.48  % (15891)------------------------------
% 0.22/0.48  % (15891)------------------------------
% 0.22/0.48  % (15883)Success in time 0.12 s
%------------------------------------------------------------------------------
