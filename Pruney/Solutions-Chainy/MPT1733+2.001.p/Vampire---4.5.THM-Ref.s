%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 (1249 expanded)
%              Number of leaves         :   14 ( 596 expanded)
%              Depth                    :   10
%              Number of atoms          :  434 (20861 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f217,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f59,f68,f69,f183,f190,f204,f216])).

fof(f216,plain,
    ( spl4_2
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f209,f89])).

fof(f89,plain,(
    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f23,f25,f24,f26,f29,f35])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f29,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
        & ( r1_tsep_1(sK3,sK2)
          | r1_tsep_1(sK3,sK1) ) )
      | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
        & ( r1_tsep_1(sK2,sK3)
          | r1_tsep_1(sK1,sK3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                        & ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) ) )
                      | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                        & ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) ) ) )
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
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
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

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2))
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X3,X1) ) )
                  | ( ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3)
                    & ( r1_tsep_1(X2,X3)
                      | r1_tsep_1(X1,X3) ) ) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2))
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X3,sK1) ) )
                | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3)
                  & ( r1_tsep_1(X2,X3)
                    | r1_tsep_1(sK1,X3) ) ) )
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2))
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X3,sK1) ) )
              | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3)
                & ( r1_tsep_1(X2,X3)
                  | r1_tsep_1(sK1,X3) ) ) )
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2))
              & ( r1_tsep_1(X3,sK2)
                | r1_tsep_1(X3,sK1) ) )
            | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3)
              & ( r1_tsep_1(sK2,X3)
                | r1_tsep_1(sK1,X3) ) ) )
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X3] :
        ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2))
            & ( r1_tsep_1(X3,sK2)
              | r1_tsep_1(X3,sK1) ) )
          | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3)
            & ( r1_tsep_1(sK2,X3)
              | r1_tsep_1(sK1,X3) ) ) )
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
          & ( r1_tsep_1(sK3,sK2)
            | r1_tsep_1(sK3,sK1) ) )
        | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
          & ( r1_tsep_1(sK2,sK3)
            | r1_tsep_1(sK1,sK3) ) ) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
                     => ( ( ( r1_tsep_1(X3,X2)
                            | r1_tsep_1(X3,X1) )
                         => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                        & ( ( r1_tsep_1(X2,X3)
                            | r1_tsep_1(X1,X3) )
                         => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
                   => ( ( ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                      & ( ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tmap_1)).

fof(f26,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f24,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f25,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f23,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f21,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f209,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f25,f28,f26,f73,f82,f49,f67,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X3,X1)
      | ~ r1_tsep_1(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f67,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_6
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f49,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_2
  <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f82,plain,(
    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f20,f22,f23,f24,f25,f26,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
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

fof(f73,plain,(
    ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f20,f22,f23,f24,f25,f26,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f204,plain,
    ( spl4_2
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f195,f88])).

fof(f88,plain,(
    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f23,f25,f24,f26,f29,f34])).

fof(f34,plain,(
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
    inference(cnf_transformation,[],[f10])).

fof(f195,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f23,f63,f24,f28,f73,f82,f49,f39])).

fof(f63,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_5
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f190,plain,
    ( spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f188,f89])).

fof(f188,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | spl4_1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f25,f28,f26,f73,f82,f45,f58,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X1,X3)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl4_4
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f45,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_1
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f183,plain,
    ( spl4_1
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl4_1
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f153,f88])).

fof(f153,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | spl4_1
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f23,f54,f24,f28,f73,f45,f82,f36])).

fof(f54,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_3
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f69,plain,
    ( spl4_3
    | spl4_4
    | spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f30,f65,f61,f56,f52])).

fof(f30,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,
    ( ~ spl4_1
    | spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f31,f65,f61,f43])).

fof(f31,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,
    ( spl4_3
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f32,f47,f56,f52])).

fof(f32,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f33,f47,f43])).

fof(f33,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (6285)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.20/0.46  % (6286)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.20/0.46  % (6275)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.20/0.47  % (6290)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (6278)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.48  % (6282)WARNING: option uwaf not known.
% 0.20/0.48  % (6282)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.49  % (6272)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.20/0.49  % (6275)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f50,f59,f68,f69,f183,f190,f204,f216])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    spl4_2 | ~spl4_6),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f215])).
% 0.20/0.49  fof(f215,plain,(
% 0.20/0.49    $false | (spl4_2 | ~spl4_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f209,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f20,f21,f22,f23,f25,f24,f26,f29,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ~r1_tsep_1(sK1,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    (((((~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) & (r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1))) | (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1))) | (~r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1))) | (~r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(sK1,X3)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(sK1,X3)))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(X3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3) & (r1_tsep_1(sK2,X3) | r1_tsep_1(sK1,X3)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2)) & (r1_tsep_1(X3,sK2) | r1_tsep_1(X3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3) & (r1_tsep_1(sK2,X3) | r1_tsep_1(sK1,X3)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (((~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) & (r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1))) | (~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) & (r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1))) | (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1))) | (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) & (r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => (((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) & ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f4])).
% 0.20/0.49  fof(f4,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => (((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) & ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tmap_1)).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    m1_pre_topc(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ~v2_struct_0(sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ~v2_struct_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (spl4_2 | ~spl4_6)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f25,f28,f26,f73,f82,f49,f67,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X3,X1) | ~r1_tsep_1(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    r1_tsep_1(sK3,sK2) | ~spl4_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl4_6 <=> r1_tsep_1(sK3,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    spl4_2 <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f20,f22,f23,f24,f25,f26,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f20,f22,f23,f24,f25,f26,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    m1_pre_topc(sK3,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ~v2_struct_0(sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    spl4_2 | ~spl4_5),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f203])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    $false | (spl4_2 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f195,f88])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f20,f21,f22,f23,f25,f24,f26,f29,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | (spl4_2 | ~spl4_5)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f23,f63,f24,f28,f73,f82,f49,f39])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    r1_tsep_1(sK3,sK1) | ~spl4_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    spl4_5 <=> r1_tsep_1(sK3,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    spl4_1 | ~spl4_4),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f189])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    $false | (spl4_1 | ~spl4_4)),
% 0.20/0.49    inference(subsumption_resolution,[],[f188,f89])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (spl4_1 | ~spl4_4)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f25,f28,f26,f73,f82,f45,f58,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X1,X3) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    r1_tsep_1(sK2,sK3) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    spl4_4 <=> r1_tsep_1(sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    spl4_1 <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    spl4_1 | ~spl4_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f182])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    $false | (spl4_1 | ~spl4_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f153,f88])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | (spl4_1 | ~spl4_3)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f23,f54,f24,f28,f73,f45,f82,f36])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    r1_tsep_1(sK1,sK3) | ~spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl4_3 <=> r1_tsep_1(sK1,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl4_3 | spl4_4 | spl4_5 | spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f30,f65,f61,f56,f52])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1) | r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ~spl4_1 | spl4_5 | spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f31,f65,f61,f43])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1) | ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    spl4_3 | spl4_4 | ~spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f32,f47,f56,f52])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ~spl4_1 | ~spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f33,f47,f43])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (6275)------------------------------
% 0.20/0.49  % (6275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (6275)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (6275)Memory used [KB]: 10106
% 0.20/0.49  % (6275)Time elapsed: 0.100 s
% 0.20/0.49  % (6275)------------------------------
% 0.20/0.49  % (6275)------------------------------
% 0.20/0.49  % (6276)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.20/0.49  % (6271)Success in time 0.141 s
%------------------------------------------------------------------------------
