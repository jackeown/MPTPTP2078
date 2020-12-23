%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:09 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 (1831 expanded)
%              Number of leaves         :   14 ( 870 expanded)
%              Depth                    :   10
%              Number of atoms          :  456 (30721 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f68,f69,f183,f192,f194,f205,f225,f227])).

fof(f227,plain,
    ( ~ spl4_4
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f218,f89])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16,f15])).

fof(f15,plain,
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

fof(f16,plain,
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

fof(f17,plain,
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

fof(f18,plain,
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

fof(f8,plain,(
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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
                     => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                         => ( ~ r1_tsep_1(X3,X2)
                            & ~ r1_tsep_1(X3,X1) ) )
                        & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                         => ( ~ r1_tsep_1(X2,X3)
                            & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
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
                   => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                       => ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X3,X1) ) )
                      & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                       => ( ~ r1_tsep_1(X2,X3)
                          & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).

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

fof(f218,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_4
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f25,f57,f26,f28,f73,f82,f67,f39])).

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
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_6
  <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

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

% (28422)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
fof(f28,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f57,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_4
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f27,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f225,plain,
    ( ~ spl4_1
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl4_1
    | spl4_6 ),
    inference(subsumption_resolution,[],[f221,f88])).

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

fof(f221,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl4_1
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f23,f45,f24,f28,f73,f82,f67,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X3,X1)
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

fof(f45,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_1
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f205,plain,
    ( ~ spl4_1
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl4_1
    | spl4_5 ),
    inference(subsumption_resolution,[],[f201,f88])).

fof(f201,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl4_1
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f23,f45,f24,f28,f73,f82,f62,f36])).

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

fof(f62,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_5
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f194,plain,
    ( ~ spl4_3
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl4_3
    | spl4_6 ),
    inference(subsumption_resolution,[],[f185,f88])).

fof(f185,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ spl4_3
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f23,f53,f24,f28,f73,f82,f67,f39])).

fof(f53,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_3
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f192,plain,
    ( ~ spl4_2
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | ~ spl4_2
    | spl4_6 ),
    inference(subsumption_resolution,[],[f188,f89])).

fof(f188,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_2
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f25,f49,f26,f28,f73,f82,f67,f37])).

fof(f49,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_2
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f183,plain,
    ( ~ spl4_2
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl4_2
    | spl4_5 ),
    inference(subsumption_resolution,[],[f153,f89])).

fof(f153,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ spl4_2
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f25,f49,f26,f28,f73,f62,f82,f36])).

fof(f69,plain,
    ( ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f30,f65,f60])).

fof(f30,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f68,plain,
    ( spl4_1
    | spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f31,f65,f47,f43])).

fof(f31,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,
    ( spl4_1
    | spl4_2
    | spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f33,f55,f51,f47,f43])).

% (28418)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
fof(f33,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:33:40 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (28421)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.48  % (28428)WARNING: option uwaf not known.
% 0.22/0.49  % (28419)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.49  % (28428)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.49  % (28423)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.50  % (28430)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.50  % (28421)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (28427)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f58,f68,f69,f183,f192,f194,f205,f225,f227])).
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    ~spl4_4 | spl4_6),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f226])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    $false | (~spl4_4 | spl4_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f218,f89])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f21,f22,f23,f25,f24,f26,f29,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tsep_1)).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ~r1_tsep_1(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ((((((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1)) & ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))) | ((r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f18,f17,f16,f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(sK1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,sK1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(sK1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : ((((r1_tsep_1(X3,sK2) | r1_tsep_1(X3,sK1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2))) | ((r1_tsep_1(sK2,X3) | r1_tsep_1(sK1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X3] : ((((r1_tsep_1(X3,sK2) | r1_tsep_1(X3,sK1)) & ~r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2))) | ((r1_tsep_1(sK2,X3) | r1_tsep_1(sK1,X3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => ((((r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1)) & ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))) | ((r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)) & ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((((r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1)) & ~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))) | ((r1_tsep_1(X2,X3) | r1_tsep_1(X1,X3)) & ~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) => (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X3,X1))) & (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) => (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X1,X3)))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f4])).
% 0.22/0.51  fof(f4,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((~r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) => (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X3,X1))) & (~r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) => (~r1_tsep_1(X2,X3) & ~r1_tsep_1(X1,X3)))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ~v2_struct_0(sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ~v2_struct_0(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    v2_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_4 | spl4_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f25,f57,f26,f28,f73,f82,f67,f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X3,X1) | ~r1_tsep_1(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | spl4_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f65])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl4_6 <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f22,f23,f24,f25,f26,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ~v2_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f22,f23,f24,f25,f26,f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  % (28422)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    r1_tsep_1(sK3,sK2) | ~spl4_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl4_4 <=> r1_tsep_1(sK3,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ~v2_struct_0(sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f225,plain,(
% 0.22/0.51    ~spl4_1 | spl4_6),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f224])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    $false | (~spl4_1 | spl4_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f221,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f21,f22,f23,f25,f24,f26,f29,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | (~spl4_1 | spl4_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f23,f45,f24,f28,f73,f82,f67,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X3,X1) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    r1_tsep_1(sK1,sK3) | ~spl4_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    spl4_1 <=> r1_tsep_1(sK1,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ~spl4_1 | spl4_5),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    $false | (~spl4_1 | spl4_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f201,f88])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | (~spl4_1 | spl4_5)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f23,f45,f24,f28,f73,f82,f62,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X1,X3) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) | spl4_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    spl4_5 <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    ~spl4_3 | spl4_6),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f193])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    $false | (~spl4_3 | spl4_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f185,f88])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1) | (~spl4_3 | spl4_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f23,f53,f24,f28,f73,f82,f67,f39])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    r1_tsep_1(sK3,sK1) | ~spl4_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f51])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    spl4_3 <=> r1_tsep_1(sK3,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    ~spl4_2 | spl4_6),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f191])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    $false | (~spl4_2 | spl4_6)),
% 0.22/0.51    inference(subsumption_resolution,[],[f188,f89])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_2 | spl4_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f25,f49,f26,f28,f73,f82,f67,f37])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    r1_tsep_1(sK2,sK3) | ~spl4_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    spl4_2 <=> r1_tsep_1(sK2,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.51  fof(f183,plain,(
% 0.22/0.51    ~spl4_2 | spl4_5),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f182])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    $false | (~spl4_2 | spl4_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f153,f89])).
% 0.22/0.51  fof(f153,plain,(
% 0.22/0.51    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2) | (~spl4_2 | spl4_5)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f20,f21,f22,f27,f25,f49,f26,f28,f73,f62,f82,f36])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ~spl4_5 | ~spl4_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f30,f65,f60])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | ~r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    spl4_1 | spl4_2 | ~spl4_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f31,f65,f47,f43])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ~r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) | r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    spl4_1 | spl4_2 | spl4_3 | spl4_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f33,f55,f51,f47,f43])).
% 0.22/0.51  % (28418)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK3,sK1) | r1_tsep_1(sK2,sK3) | r1_tsep_1(sK1,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (28421)------------------------------
% 0.22/0.51  % (28421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28421)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (28421)Memory used [KB]: 10234
% 0.22/0.51  % (28421)Time elapsed: 0.075 s
% 0.22/0.51  % (28421)------------------------------
% 0.22/0.51  % (28421)------------------------------
% 0.22/0.51  % (28417)Success in time 0.152 s
%------------------------------------------------------------------------------
